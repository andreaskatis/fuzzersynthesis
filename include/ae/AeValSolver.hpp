#ifndef AEVALSOLVER__HPP__
#define AEVALSOLVER__HPP__
#include <assert.h>

#include "ae/SMTUtils.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
namespace ufo
{
  
  /** engine to solve validity of \forall-\exists formulas and synthesize Skolem relation */
  
  class AeValSolver {
  private:

    Expr s;
    Expr t;
    ExprVector randSanityExprs; //Andreas : Preconditions for nondet synthesis
    ExprSet v; // existentially quantified vars
    ExprVector sVars;
    ExprVector stVars;

    ExprSet tConjs;
    ExprSet usedConjs;
    ExprMap defMap;
    ExprMap cyclicDefs;
    ExprMap modelInvalid;

    ExprFactory &efac;
    EZ3 z3;
    ZSolver<EZ3> smt;
    SMTUtils u;

    unsigned partitioning_size;
    ExprVector projections;
    ExprVector instantiations;
    vector<ExprMap> skolMaps;
    vector<ExprMap> someEvals;
    Expr skolSkope;
    ExprSet sensitiveVars; // for compaction
    set<int> bestIndexes; // for compaction
    map<Expr, ExprVector> skolemConstraints;

    bool skol;
    bool debug;
    //Andreas option for nondeterministic synthesis
    bool nondet;
    unsigned fresh_var_ind;

  public:

    AeValSolver (Expr _s, Expr _t, ExprSet &_v, bool _debug, bool _skol, bool _nondet) :
      s(_s), t(_t), v(_v),
      efac(s->getFactory()),
      z3(efac),
      smt (z3),
      u(efac),
      fresh_var_ind(0),
      partitioning_size(0),
      skol(_skol),
      debug(_debug),
      nondet(_nondet)
    {
      filter (s, bind::IsConst (), back_inserter (sVars));
      filter (boolop::land(s,t), bind::IsConst (), back_inserter (stVars));
      getConj(t, tConjs);

      for (auto &exp: v) {
        if (!bind::isBoolConst(exp)) continue;
        Expr definition = getBoolDefinitionFormulaFromT(exp);
        if (definition != NULL) defMap[exp] = u.simplifyITE(definition);
      }

      for (auto &exp: v) {
        if (defMap[exp] != NULL) continue;
        Expr definition = getDefinitionFormulaFromT(exp);
        if (definition != NULL) defMap[exp] = u.simplifyITE(definition);
      }

      splitDefs(defMap, cyclicDefs);
      skolSkope = mk<TRUE>(efac);
    }

    void splitDefs (ExprMap &m1, ExprMap &m2, int curCnt = 0)
    {
      ExprMap m3;
      ExprMap m4;
      for (auto & a : m1)
      {
        if (a.second == NULL) continue;
        if (emptyIntersect(a.second, v))
        {
          m3.insert(a);
        }
        else
        {
          m4.insert(a);
        }
      }
      if (m3.size() == curCnt)
      {
        m2 = m4;
        return;
      }

      for (auto & a : m3)
      {
        for (auto & b : m1)
        {
          if (b.second == NULL) continue;
          if (a.first != b.first)
          {
            b.second = replaceAll(b.second, a.first, a.second);
          }
        }
      }
      splitDefs(m1, m2, m3.size());
    }

    /**
     * Decide validity of \forall s => \exists v . t
     */
    boost::tribool solve ()
    {
      smt.reset();
      smt.assertExpr (s);

      if (!smt.solve ()) {
        return false;
      } else {
        ZSolver<EZ3>::Model m = smt.getModel();

        for (auto &e: sVars)
          // keep a model in case the formula is invalid
          modelInvalid[e] = m.eval(e);
      }

      if (v.size () == 0)
      {
        smt.assertExpr (boolop::lneg (t));
        boost::tribool res = smt.solve ();
        return res;
      }

      smt.push ();
      smt.assertExpr (t);

      boost::tribool res = true;

      while (smt.solve ())
      {
        outs().flush ();

        ZSolver<EZ3>::Model m = smt.getModel();

        if (debug && false)
        {
          outs() << "\nmodel " << partitioning_size << ":\n";
          for (auto &exp: stVars)
          {
            if (exp != m.eval(exp))
              outs() << "[" << *exp << "=" << *m.eval(exp) << "],";
          }
          outs() <<"\n";
        }

        getMBPandSkolem(m, t, v, ExprMap());

        smt.pop();
        smt.assertExpr(boolop::lneg(projections.back()));
        if (!smt.solve()) {
          res = false; break;
        } else {
          // keep a model in case the formula is invalid
          m = smt.getModel();
          for (auto &e: sVars)
            modelInvalid[e] = m.eval(e);
        }

        smt.push();
        smt.assertExpr (t);
      }
      return res;
    }

    /**
     * Extract MBP and local Skolem
     */
    void getMBPandSkolem(ZSolver<EZ3>::Model &m, Expr pr, ExprSet tmpVars, ExprMap substsMap)
    {
      ExprMap modelMap;
      for (auto exp = tmpVars.begin(); exp != tmpVars.end();)
      {
        ExprMap map;
        pr = z3_qe_model_project_skolem (z3, m, *exp, pr, map);
        if (skol) getLocalSkolems(m, *exp, map, substsMap, modelMap, pr);
        Expr var = *exp;
        tmpVars.erase(exp++);
      }

      if (debug) assert(emptyIntersect(pr, v));

      someEvals.push_back(modelMap);
      skolMaps.push_back(substsMap);
      projections.push_back(pr);
      partitioning_size++;
    }

    void fillSubsts (Expr ef, Expr es, Expr mbp, ExprSet& substs)
    {
      if (!sameBoolOrCmp(ef, es))
      {
        substs.insert(mk<EQ>(ineqNegReverter(ef), ineqNegReverter(es)));
      }
      else if (isOpX<FALSE>(es))
      {
        // useless (just for optim)
      }
      else if (isOpX<TRUE>(es) || u.implies(mbp, es))
      {
        substs.insert(ineqNegReverter(ef));
      }
    }

    /**
     * Compute local skolems based on the model
     */
    void getLocalSkolems(ZSolver<EZ3>::Model &m, Expr exp,
                           ExprMap &map, ExprMap &substsMap, ExprMap &modelMap, Expr& mbp)
    {
      if (map.size() > 0){
        ExprSet substs;
        for (auto &e: map) fillSubsts(e.first, e.second, mbp, substs);
        if (substs.size() == 0)
        {
          if (debug) outs() << "WARNING: subst is empty for " << *exp << "\n";
        }
        else
        {
          substsMap[exp] = conjoin(substs, efac);
        }
      }
      if (m.eval(exp) != exp){
        modelMap[exp] = mk<EQ>(exp, m.eval(exp));
      }
    }

    bool sameBoolOrCmp (Expr ef, Expr es)
    {
      return (isOp<BoolOp>(ef) && isOp<BoolOp>(es)) ||
         (isOp<ComparissonOp>(ef) && isOp<ComparissonOp>(es)) ||
         (isOp<BoolOp>(ef) && isOp<ComparissonOp>(es)) ||
         (isOp<ComparissonOp>(ef) && isOp<BoolOp>(es));
    }

    /**
     * Valid Subset of S (if overall AE-formula is invalid)
     */
    Expr getValidSubset()
    {
      if (partitioning_size == 0){
//        outs() << "WARNING: Trivial valid subset (equal to False) due to 0 iterations\n";
        return mk<FALSE>(efac);
      }
      return mk<AND>(s, disjoin(projections, efac));
    }

    /**
     * Model of S /\ \neg T (if AE-formula is invalid)
     */
    void printModelNeg()
    {
      outs () << "(model\n";
      Expr s_witn = s;
      Expr t_witn = t;
      for (auto &var : sVars){
        Expr assnmt = var == modelInvalid[var] ? getDefaultAssignment(var) : modelInvalid[var];
        if (debug) {
          s_witn = replaceAll(s_witn, var, assnmt);
          t_witn = replaceAll(t_witn, var, assnmt);
        }

        outs () << "  (define-fun " << *var << " () " <<
          (bind::isBoolConst(var) ? "Bool" : (bind::isIntConst(var) ? "Int" : "Real"))
                << "\n    " << *assnmt << ")\n";
      }
      outs () << ")\n";

      if (debug){
        outs () << "Sanity check [model, S-part]: " << !(u.isSat(mk<NEG>(s_witn))) << "\n";
        outs () << "Sanity check [model, T-part]: " << !(u.isSat(t_witn)) << "\n";
      }
    }

    /**
     * Mine the structure of T to get what was assigned to a variable
     */
    Expr getDefinitionFormulaFromT(Expr var)
    {
      ExprSet defs;
      for (auto & cnj : tConjs)
      {
        // get equality (unique per variable)
        if (std::find(std::begin(usedConjs),
                      std::end  (usedConjs), cnj) != std::end(usedConjs)) continue;

        if (isOpX<EQ>(cnj))
        {
          if (var == cnj->left() || var == cnj->right())
          {
            defs.insert(cnj);
          }
        }
      }

      // now find `the best` one

      if (defs.empty()) return NULL;

      Expr def = *defs.begin();
      for (auto & a : defs)
      {
        if (!emptyIntersect(a, sVars)) def = a;
      }

      usedConjs.insert(def);
      return (var == def->left() ? def->right() : def->left());
    }

    /**
     * Mine the structure of T to get what was assigned to a variable
     */
    Expr getBoolDefinitionFormulaFromT(Expr var)
    {
      Expr def;
      for (auto & cnj : tConjs)
      {
        if (std::find(std::begin(usedConjs),
                      std::end  (usedConjs), cnj) != std::end(usedConjs)) continue;

        if (bind::isBoolConst(cnj) && var == cnj)
        {
          def = mk<TRUE>(efac);
          usedConjs.insert(cnj);
        }
        else if (isOpX<NEG>(cnj) && bind::isBoolConst(cnj->left()) && var == cnj->left())
        {
          def = mk<FALSE>(efac);
          usedConjs.insert(cnj);
        }
      }

      if (def != NULL) extendTWithDefs(var, def);
      return def;
    }

    void extendTWithDefs(Expr var, Expr def)
    {
      for (auto & cnj : tConjs)
      {
        if (std::find(std::begin(usedConjs),
                      std::end  (usedConjs), cnj) != std::end(usedConjs)) continue;

        if (isOpX<EQ>(cnj))
        {
          if (var == cnj->left())
          {
            usedConjs.insert(cnj);
            if (def == NULL)
            {
              def = cnj->right();
              break;
            }
            else
            {
              getConj(isOpX<TRUE>(def) ? cnj->right() : mk<NEG> (cnj->right()), tConjs);
            }
          }
          else if (var == cnj->right())
          {
            usedConjs.insert(cnj);
            if (def == NULL)
            {
              def = cnj->left();
              break;
            }
            else
            {
              getConj(isOpX<TRUE>(def) ? cnj->left() : mk<NEG> (cnj->left()), tConjs);
            }
          }

          if (debug && tConjs.empty())
            outs () << "WARNING: getBoolDefinitionFormulaFromT has cleared tConjs\n";
        }
      }
    }

    /**
     * Mine the structure of T `conditionally`
     */
    Expr getCondDefinitionFormula(Expr var, Expr pre)
    {
      Expr res = NULL;
      ExprSet eqs;
      ExprSet eqsFilt;
      getEqualities(t, var, eqs);
      for (auto a : eqs)
      {
        if (u.implies(pre, a) && !u.isEquiv(a, mk<TRUE>(efac))) eqsFilt.insert(a);
      }

      int maxSz = 0;
      for (auto & a : eqsFilt) if (boolop::circSize(a) > maxSz) res = a;
      return res;
    }

    /**
     * Self explanatory
     */
    void GetSymbolicMax(ExprSet& vec, Expr& curMax, bool isInt)
    {
      curMax = *vec.begin();
      for (auto it = vec.begin(); ++it != vec.end(); ){
        auto &a = *it;
        if (u.isEquiv(mk<LT>(curMax, a), mk<TRUE>(efac))){
          curMax = a;
        } else if (u.isEquiv(mk<LT>(curMax, a), mk<FALSE>(efac))){
          //  curMax is OK
        } else {
          string ind = lexical_cast<string> (fresh_var_ind++);

          Expr varName = mkTerm ("_aeval_tmp_max_" + ind, efac);
          Expr var = isInt ? bind::intConst(varName) : bind::realConst(varName);

          Expr newConstr = mk<EQ>(var, mk<ITE>(mk<LT>(curMax, a), a, curMax));
          skolSkope = simplifiedAnd(skolSkope, newConstr);

          curMax = var;
        }
      }
    }

    /**
     * Self explanatory
     */
    void GetSymbolicMin(ExprSet& vec, Expr& curMin, bool isInt)
    {
      curMin = *vec.begin();
      for (auto it = vec.begin(); ++it != vec.end(); ){
        auto &a = *it;
        if (u.isEquiv(mk<GT>(curMin, a), mk<TRUE>(efac))){
          curMin = a;
        } else if (u.isEquiv(mk<GT>(curMin, a), mk<FALSE>(efac))){
          //  curMin is OK
        } else {
          string ind = lexical_cast<string> (fresh_var_ind++);

          Expr varName = mkTerm ("_aeval_tmp_min_" + ind, efac);
          Expr var = isInt ? bind::intConst(varName) : bind::realConst(varName);

          Expr newConstr = mk<EQ>(var, mk<ITE>(mk<GT>(curMin, a), a, curMin));
          skolSkope = simplifiedAnd(skolSkope, newConstr);
          curMin = var;
        }
      }
    }
    
    void GetSymbolicNeq(ExprSet& vec, Expr& lower, Expr& upper, Expr& candidate, bool strict, bool isInt)
    {
      Expr var1 = lower;
      Expr eps;
      if (isInt)
        eps = mkTerm (mpz_class (1), efac);
      else
        eps = mk<DIV>(mk<MINUS>(upper, lower), mkTerm (mpq_class (vec.size() + 2), efac));

      if (strict) var1 = mk<PLUS>(var1, eps);

      string ind = lexical_cast<string> (fresh_var_ind++);
      Expr varName = mkTerm ("_aeval_tmp_neg_" + ind, efac);
      Expr var2 = isInt ? bind::intConst(varName) : bind::realConst(varName);

      candidate = var2;
      for (int i = 0; i <= vec.size(); i++)
      {
        ExprSet neqqedConstrs;
        for (auto &a : vec) neqqedConstrs.insert(mk<EQ>(a, var1));

        string ind = lexical_cast<string> (fresh_var_ind++);
        Expr varName = mkTerm ("_aeval_tmp_neg_" + ind, efac);
        Expr newVar = isInt ? bind::intConst(varName) : bind::realConst(varName);

        Expr newConstr = mk<EQ>(var2, mk<ITE>(disjoin(neqqedConstrs, efac), newVar, var1));
        skolSkope = simplifiedAnd(skolSkope, newConstr);

        var1 = mk<PLUS>(var1, eps);
        var2 = newVar;
      }
    }
    
    // void GetSymbolicNeqNonDet(ExprSet& vec, Expr& lower, Expr& upper, Expr& candidate, bool lflag, bool uflag, bool isInt)
    void GetSymbolicNeqNonDet(ExprSet& vec, Expr& lower, Expr& upper, Expr& candidate, Expr& lflag, Expr& uflag, bool isInt)
    {
      string ind = lexical_cast<string> (fresh_var_ind++);
      if (isInt)
        {
        ExprVector intArgs;
        Expr randNameInt = mkTerm ("_aeval_tmp_randneq_int_" + ind, efac);
        for (auto &a : vec) intArgs.push_back(sort::intTy (efac)); 
        intArgs.push_back(sort::boolTy (efac));
        intArgs.push_back(sort::boolTy (efac));
        intArgs.push_back(sort::intTy (efac));
        intArgs.push_back(sort::intTy (efac));
        intArgs.push_back(sort::intTy (efac));
        Expr randInt = bind::fdecl(randNameInt, intArgs);

        ExprVector args;
        for (auto &a : vec) {
          args.push_back(a);
        }
        // lflag ? args.push_back(mk<FALSE> (efac)) : args.push_back(mk<TRUE> (efac));
        // uflag ? args.push_back(mk<FALSE> (efac)) : args.push_back(mk<TRUE> (efac));
        args.push_back(lflag);
        args.push_back(uflag);
        args.push_back(lower);
        args.push_back(upper);
        Expr randIntApp = bind::fapp(randInt, args);

        candidate = randIntApp;

        Expr lExpr;
        Expr uExpr;
        // if (lflag) {
        //   lExpr = mk<GEQ>(randIntApp, lower);
        // } else {
        //   lExpr = mk<GT>(randIntApp, lower);
        // }
        // if (uflag) {
        //   uExpr = mk<LEQ>(randIntApp, upper);
        // } else {
        //   uExpr = mk<LT>(randIntApp, upper);
        // }
        lExpr = mk<ITE>(lflag, mk<GEQ>(randIntApp, lower), mk<GT>(randIntApp, lower));
        uExpr = mk<ITE>(uflag, mk<LEQ>(randIntApp, upper), mk<LT>(randIntApp, upper));
        

        randSanityExprs.push_back(mk<AND>(lExpr, uExpr));
        for (auto &a : vec) randSanityExprs.push_back(mk<NEQ>(randIntApp, a));
      }

      else
      {
        ExprVector realArgs;
        Expr randNameReal = mkTerm ("_aeval_tmp_randneq_real_" + ind, efac);
        for (auto &a : vec) realArgs.push_back(sort::realTy (efac));
        realArgs.push_back(sort::boolTy (efac));
        realArgs.push_back(sort::boolTy (efac));
        realArgs.push_back(sort::realTy (efac));
        realArgs.push_back(sort::realTy (efac));
        realArgs.push_back(sort::realTy (efac));
        Expr randReal = bind::fdecl(randNameReal, realArgs);

        ExprVector args;
        for (auto &a : vec) {
          args.push_back(a);
        }
        // lflag ? args.push_back(mk<FALSE> (efac)) : args.push_back(mk<TRUE> (efac));
        // uflag ? args.push_back(mk<FALSE> (efac)) : args.push_back(mk<TRUE> (efac));
        args.push_back(lflag);
        args.push_back(uflag);
        args.push_back(lower);
        args.push_back(upper);
        Expr randRealApp = bind::fapp(randReal, args);
        
        candidate = randRealApp;
        Expr lExpr;
        Expr uExpr;
        // if (lflag) {
        //   lExpr = mk<GEQ>(randRealApp, lower);
        // } else {
        //   lExpr = mk<GT>(randRealApp, lower);
        // }
        // if (uflag) {
        //   uExpr = mk<LEQ>(randRealApp, upper);
        // } else {
        //   uExpr = mk<LT>(randRealApp, upper);
        // }
        lExpr = mk<ITE>(lflag, mk<GEQ>(randRealApp, lower), mk<GT>(randRealApp, lower));
        uExpr = mk<ITE>(uflag, mk<LEQ>(randRealApp, upper), mk<LT>(randRealApp, upper));
        
        randSanityExprs.push_back(mk<AND>(lExpr, uExpr));
        for (auto &a : vec) randSanityExprs.push_back(mk<NEQ>(randRealApp, a));
      }      
    }

    /**
     * Based on type
     */
    Expr getDefaultAssignment(Expr var)
    {
      if (bind::isBoolConst(var)) return mk<TRUE>(efac);
      if (bind::isIntConst(var)) return mkTerm (mpz_class (0), efac);
      else           // that is, isRealConst(var) == true
        return mkTerm (mpq_class (0), efac);
    }

    /**
     * Return "e + eps"
     */
    Expr plusEps(Expr e, bool isInt, bool closed)
    {
  		if (nondet) {
      	string ind = lexical_cast<string> (fresh_var_ind++);
        if(isInt) {
          ExprVector intArgs;
          Expr randNameInt = mkTerm ("_aeval_tmp_rand_int_" + ind, efac); 
          intArgs.push_back(sort::boolTy (efac));
          intArgs.push_back(sort::boolTy (efac));
          intArgs.push_back(sort::intTy (efac));
          intArgs.push_back(sort::intTy (efac));
          intArgs.push_back(sort::intTy (efac));
          Expr randInt = bind::fdecl(randNameInt, intArgs);


          ExprVector args;
          args.push_back(mk<FALSE>(efac));
          args.push_back(mk<FALSE>(efac));
          args.push_back(mkTerm (mpz_class (0), efac));
          args.push_back(mkTerm (mpz_class (0), efac));
          Expr randIntApp = bind::fapp(randInt, args);
          if (closed) {
            randSanityExprs.push_back(mk<GEQ>(randIntApp, mkTerm (mpz_class (0), efac)));
          } else {
            randSanityExprs.push_back(mk<GT>(randIntApp, mkTerm (mpz_class (0), efac)));
          }
          return mk<PLUS>(e, randIntApp);	          
        } else {
          ExprVector realArgs;
          Expr randNameReal = mkTerm ("_aeval_tmp_rand_real_" + ind, efac);
          realArgs.push_back(sort::boolTy (efac));
          realArgs.push_back(sort::boolTy (efac));
          realArgs.push_back(sort::realTy (efac));
          realArgs.push_back(sort::realTy (efac));
          realArgs.push_back(sort::realTy (efac));
          Expr randReal = bind::fdecl(randNameReal, realArgs);

          ExprVector args;
          args.push_back(mk<FALSE>(efac));
          args.push_back(mk<FALSE>(efac));
          args.push_back(mkTerm (mpq_class (0), efac));
          args.push_back(mkTerm (mpq_class (0), efac));
          Expr randRealApp = bind::fapp(randReal, args);
          if (closed) {
            randSanityExprs.push_back(mk<GEQ>(randRealApp, mkTerm (mpq_class (0), efac)));
          } else {
            randSanityExprs.push_back(mk<GT>(randRealApp, mkTerm (mpq_class (0), efac)));
          }
          return mk<PLUS>(e, randRealApp);
        }
  		} else {
	      if (isOpX<MPZ>(e) && isInt)	return mkTerm (mpz_class (boost::lexical_cast<int> (e) + 1), efac);
	  		if (isInt) return mk<PLUS>(e, mkTerm (mpz_class (1), efac));
	  		else return mk<PLUS>(e, mkTerm (mpq_class (1), efac));
  		}
    }

    /**
     * Return "e - eps"
     */
    Expr minusEps(Expr e, bool isInt, bool closed)
    {
    	if (nondet) {
		  string ind = lexical_cast<string> (fresh_var_ind++);
		  if(isInt) {
	        ExprVector intArgs;
	        Expr randNameInt = mkTerm ("_aeval_tmp_rand_int_" + ind, efac); 
	        intArgs.push_back(sort::boolTy (efac));
	        intArgs.push_back(sort::boolTy (efac));
	        intArgs.push_back(sort::intTy (efac));
	        intArgs.push_back(sort::intTy (efac));
	        intArgs.push_back(sort::intTy (efac));
	        Expr randInt = bind::fdecl(randNameInt, intArgs);

	        ExprVector args;
	        args.push_back(mk<FALSE>(efac));
	        args.push_back(mk<FALSE>(efac));
	        args.push_back(mkTerm (mpz_class (0), efac));
	        args.push_back(mkTerm (mpz_class (0), efac));
	        Expr randIntApp = bind::fapp(randInt, args);
          if (closed) {
            randSanityExprs.push_back(mk<GEQ>(randIntApp, mkTerm (mpz_class (0), efac)));
          } else {
  	        randSanityExprs.push_back(mk<GT>(randIntApp, mkTerm (mpz_class (0), efac)));
          }
	        return mk<MINUS>(e, randIntApp);
	      } else {
	        ExprVector realArgs;
	        Expr randNameReal = mkTerm ("_aeval_tmp_rand_real_" + ind, efac);
	        realArgs.push_back(sort::boolTy (efac));
	        realArgs.push_back(sort::boolTy (efac));
	        realArgs.push_back(sort::realTy (efac));
	        realArgs.push_back(sort::realTy (efac));
	        realArgs.push_back(sort::realTy (efac));
	        Expr randReal = bind::fdecl(randNameReal, realArgs);

	        ExprVector args;
	        args.push_back(mk<FALSE>(efac));
	        args.push_back(mk<FALSE>(efac));
	        args.push_back(mkTerm (mpq_class (0), efac));
	        args.push_back(mkTerm (mpq_class (0), efac));
	        Expr randRealApp = bind::fapp(randReal, args);
          if (closed) {
            randSanityExprs.push_back(mk<GEQ>(randRealApp, mkTerm (mpq_class (0), efac)));
          } else {
            randSanityExprs.push_back(mk<GT>(randRealApp, mkTerm (mpq_class (0), efac)));
	        }
          return mk<MINUS>(e, randRealApp);       
	      }
  		} else {
        if (isOpX<MPZ>(e) && isInt)
          return mkTerm (mpz_class (boost::lexical_cast<int> (e) - 1), efac);

        if (isInt) return mk<MINUS>(e, mkTerm (mpz_class (1), efac));
        else return mk<MINUS>(e, mkTerm (mpq_class (1), efac));
      }
    }

    /**
     * Extract function from relation
     */
    Expr getAssignmentForVar(Expr var, Expr exp)
    {
      if (!isNumeric(var))
      {
        if (isOpX<EQ>(exp))
        {
          if (var == exp->left()) return exp->right();
          if (var == exp->right()) return exp->left();
        }
        outs () << "getAssignmentForVar " << *var << " in:\n" << *exp << "\n";
        assert(0);
      }

      // if (debug) outs () << "getAssignmentForVar " << *var << " in:\n" << *exp << "\n";

      bool isInt = bind::isIntConst(var);

      if (isOp<ComparissonOp>(exp))
      {
        if (isOpX<NEG>(exp)) exp = mkNeg(exp->left());

        if (!bind::isBoolConst(var) && var != exp->left())
          exp = ineqReverter(ineqMover(exp, var));
        // TODO: write a similar simplifier fo booleans

        assert (var == exp->left());
        if (isOp<EQ>(exp)) {
          if (exp->left() == exp->right()) return getDefaultAssignment(var);
          return exp->right();
        }
        else if ((isOpX<GEQ>(exp) || isOpX<LEQ>(exp))) {
          if (nondet) {
            if (isOpX<GEQ>(exp)) {
              return plusEps(exp->right(), isInt, true);
            } else {
              return minusEps(exp->right(), isInt, true);
            }
          } else {
            if (exp->left() == exp->right()) return getDefaultAssignment(var);
            return exp->right();          
          }
        }  
        else if (isOpX<LT>(exp)){
          return minusEps (exp->right(), isInt, false);
        }
        else if (isOpX<GT>(exp)){
          return plusEps (exp->right(), isInt, false);
        }
        else if (isOpX<NEQ>(exp)){
          return plusEps (exp->right(), isInt, false);
        }
        else assert(0);
      }
      else if (isOpX<NEG>(exp)){
        if (isOpX<EQ>(exp->left())) {
          return plusEps (getAssignmentForVar(var, exp->left()), isInt, false);
        }
      }
      else if (isOpX<AND>(exp))
      {
      	//Andreas : the following line would prevent having random values for closed bounds containing numerals
        if (!nondet) {
          exp = u.numericUnderapprox(exp); // try to see if there are only numerals
        }
        if (isOpX<EQ>(exp)) return exp->right();

        bool incomplete = false;

        // split constraints
        ExprSet conjLT;
        ExprSet conjLE;
        ExprSet conjGT;
        ExprSet conjGE;
        ExprSet conjNEQ;
        ExprSet conjEQ;
        ExprSet cnjs;
        getConj (exp, cnjs);
        u.removeRedundantConjuncts(cnjs);
        for (auto cnj : cnjs)
        {
          if (isOpX<NEG>(cnj)) cnj = mkNeg(cnj->left());
          cnj = ineqReverter(ineqMover(cnj, var));

          if (isOpX<EQ>(cnj)){
            if (var == cnj->left()) {
              conjEQ.insert(cnj->right());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<LT>(cnj)){
            if (var == cnj->left()) {
              if (isInt) {
              	conjLT.insert(cnj->right());              	
              } else {
              	conjLE.insert(cnj->right());
              	conjNEQ.insert(cnj->right());
              }
            } else if (var == cnj->right()) {
              if (isInt) {
              	conjGT.insert(cnj->left());
              } else {
              	conjGE.insert(cnj->left());
              	conjNEQ.insert(cnj->left());
              }
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<LEQ>(cnj)){
            if (var == cnj->left()) {
              conjLE.insert(cnj->right());
            } else if (var == cnj->right()) {
              conjGE.insert(cnj->left());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<GT>(cnj)){
            if (var == cnj->left()) {
              if (isInt) {
              	conjGT.insert(cnj->right());
              } else {
              	conjGE.insert(cnj->right());
              	conjNEQ.insert(cnj->right());
              }
            } else if (var == cnj->right()) {
              if (isInt) {
              	conjLT.insert(cnj->left());
              } else {
              	conjLE.insert(cnj->left());
              	conjNEQ.insert(cnj->left());
              }
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<GEQ>(cnj)){
            if (var == cnj->left()) {
              conjGE.insert(cnj->right());
            } else if (var == cnj->right()) {
              conjLE.insert(cnj->left());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<NEQ>(cnj)){
            if (var == cnj->left()) {
              conjNEQ.insert(cnj->right());
            } else {
              incomplete = true;
            }
          }

          if (incomplete && debug)
            outs() << "WARNING: This constraint is unsupported: " << *cnj << "\n";
        }

        // simplify some:
        for (auto & b : conjLE)
        {
          bool toBrk = false;
          for (auto & a : conjNEQ)
          {
            if (a == b)
            {
              conjLT.insert(a);
              conjNEQ.erase(a);
              conjLE.erase(b);
              toBrk = true;
              break;
            }
          }
          if (toBrk) break;
        }

        // simplify some:
        for (auto & b : conjGE)
        {
          bool toBrk = false;
          for (auto & a : conjNEQ)
          {
            if (a == b)
            {
              conjGT.insert(a);
              conjNEQ.erase(a);
              conjGE.erase(b);
              toBrk = true;
              break;
            }
          }
          if (toBrk) break;
        }

        // get the assignment (if exists)

        if (conjEQ.size() > 0) return *(conjEQ.begin()); // GF: maybe try to find the best of them

        // get symbolic max and min

        Expr curMaxGT;
        if (conjGT.size() > 1){
          GetSymbolicMax(conjGT, curMaxGT, isInt);
        } else if (conjGT.size() == 1){
          curMaxGT = *(conjGT.begin());
        }

        Expr curMaxGE;
        if (conjGE.size() > 1){
          GetSymbolicMax(conjGE, curMaxGE, isInt);
        } else if (conjGE.size() == 1){
          curMaxGE = *(conjGE.begin());
        }

        Expr curMinLT;
        if (conjLT.size() > 1){
          GetSymbolicMin(conjLT, curMinLT, isInt);
        } else if (conjLT.size() == 1){
          curMinLT = *(conjLT.begin());
        }

        Expr curMinLE;
        if (conjLE.size() > 1){
          GetSymbolicMin(conjLE, curMinLE, isInt);
        } else if (conjLE.size() == 1){
          curMinLE = *(conjLE.begin());
        }

        // get value in the middle of max and min

        Expr curMax;
        Expr curMin;

        if (curMaxGT != NULL && curMaxGE != NULL){
          curMax = mk<ITE>(mk<GT>(curMaxGT, curMaxGE), curMaxGT, curMaxGE);
        }
        else if (curMaxGT != NULL) curMax = curMaxGT;
        else curMax = curMaxGE;

        if (curMinLT != NULL && curMinLE != NULL){
          curMin = mk<ITE>(mk<LT>(curMinLT, curMinLE), curMinLT, curMinLE);
        }
        else if (curMinLT != NULL) curMin = curMinLT;
        else curMin = curMinLE;

        if (conjNEQ.size() == 0)
        {
          if (curMinLT != NULL && curMinLE == NULL && curMaxGT == NULL && curMaxGE == NULL)
          {
            return minusEps(curMinLT, isInt, false);
          }

          if (curMinLT == NULL && curMinLE == NULL && curMaxGT != NULL && curMaxGE == NULL)
          {
            return plusEps(curMaxGT, isInt, false);
          }

          if (curMinLT != NULL && curMinLE != NULL && curMaxGT == NULL && curMaxGE == NULL)
          {
            return minusEps(curMin, isInt, false);
          }

          if (curMinLT == NULL && curMinLE == NULL && curMaxGT != NULL && curMaxGE != NULL)
          {
            return plusEps(curMax, isInt, false);
          }

          if (curMinLT != NULL && curMinLE == NULL && curMaxGT != NULL && curMaxGE == NULL)
          {
          	if (nondet) {
		        string ind = lexical_cast<string> (fresh_var_ind++);

		        if (isInt) {
			        ExprVector intArgs;          
			        Expr randNameInt = mkTerm ("_aeval_tmp_rand_int_" + ind, efac); 
			        intArgs.push_back(sort::boolTy (efac));
			        intArgs.push_back(sort::boolTy (efac));
			        intArgs.push_back(sort::intTy (efac));
			        intArgs.push_back(sort::intTy (efac));
			        intArgs.push_back(sort::intTy (efac));
			        Expr randInt = bind::fdecl(randNameInt, intArgs);

		      		ExprVector args;
		  			args.push_back(mk<FALSE>(efac));
		  			args.push_back(mk<FALSE>(efac));
						  args.push_back(curMaxGT);
			      	args.push_back(curMinLT);
			  		  Expr randIntApp = bind::fapp(randInt, args);
			      	randSanityExprs.push_back(mk<AND>(mk<GT>(randIntApp, curMaxGT), mk<LT>(randIntApp, curMinLT)));
		  	  		return randIntApp;
		      	} else {
			        ExprVector realArgs;          
			        Expr randNameReal = mkTerm ("_aeval_tmp_rand_real_" + ind, efac);
			        realArgs.push_back(sort::boolTy (efac));
			        realArgs.push_back(sort::boolTy (efac));
			        realArgs.push_back(sort::realTy (efac));
			        realArgs.push_back(sort::realTy (efac));
			        realArgs.push_back(sort::realTy (efac));
			        Expr randReal = bind::fdecl(randNameReal, realArgs);

		      		ExprVector args;
		  			args.push_back(mk<FALSE>(efac));
		  			args.push_back(mk<FALSE>(efac));
						args.push_back(curMaxGT);
			      	args.push_back(curMinLT);
			  		Expr randRealApp = bind::fapp(randReal, args);
			      	randSanityExprs.push_back(mk<AND>(mk<GT>(randRealApp, curMaxGT), mk<LT>(randRealApp, curMinLT)));
		  	  		return randRealApp;
		      	}
	      	} else {
	      		if (isInt)
	      			return mk<IDIV>(mk<PLUS>(curMinLT, curMaxGT), mkTerm (mpz_class (2), efac));
            	else
              		return mk<DIV>(mk<PLUS>(curMinLT, curMaxGT), mkTerm (mpq_class (2), efac));
	      	}
          }

          if (curMinLT == NULL && curMinLE != NULL && curMaxGT == NULL && curMaxGE != NULL)
          {
          	if (nondet) {
	            string ind = lexical_cast<string> (fresh_var_ind++);

	            if (isInt) {
		            Expr randNameInt = mkTerm ("_aeval_tmp_rand_int_" + ind, efac);
		            ExprVector intArgs;
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            Expr randInt = bind::fdecl(randNameInt, intArgs);

  		      		ExprVector args;
  	      			args.push_back(mk<TRUE>(efac));
  	      			args.push_back(mk<TRUE>(efac));
                args.push_back(curMaxGE);
  			      	args.push_back(curMinLE);
                Expr randIntApp = bind::fapp(randInt, args);
  			      	randSanityExprs.push_back(mk<AND>(mk<GEQ>(randIntApp, curMaxGE), mk<LEQ>(randIntApp, curMinLE)));
  		  	  		return randIntApp;
	          	} else {
	          		ExprVector realArgs;
	            	Expr randNameReal = mkTerm ("_aeval_tmp_rand_real_" + ind, efac);
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            Expr randReal = bind::fdecl(randNameReal, realArgs);

	  	      		ExprVector args;
                args.push_back(mk<TRUE>(efac));
                args.push_back(mk<TRUE>(efac));
	  		  	   	args.push_back(curMaxGE);
                args.push_back(curMinLE);
                Expr randRealApp = bind::fapp(randReal, args);
		      	    randSanityExprs.push_back(mk<AND>(mk<GEQ>(randRealApp, curMaxGE), mk<LEQ>(randRealApp, curMinLE)));
		  	  		  return randRealApp;
	          	}
          	} else {
	            if (isInt)
              		return mk<IDIV>(mk<PLUS>(curMinLE, curMaxGE), mkTerm (mpz_class (2), efac));
            	else
              		return mk<DIV>(mk<PLUS>(curMinLE, curMaxGE), mkTerm (mpq_class (2), efac));
          	}
          }

          if (curMinLT == NULL && curMinLE != NULL && curMaxGT != NULL && curMaxGE == NULL)
          {
          	if (nondet) {
          		string ind = lexical_cast<string> (fresh_var_ind++);
 
            	if (isInt) {
            		ExprVector intArgs;
		            Expr randNameInt = mkTerm ("_aeval_tmp_rand_int_" + ind, efac); 
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            Expr randInt = bind::fdecl(randNameInt, intArgs);

		            ExprVector args;
	      			args.push_back(mk<FALSE>(efac));
	      			args.push_back(mk<TRUE>(efac));
	  				args.push_back(curMaxGT);
			      	args.push_back(curMinLE);
			  		Expr randIntApp = bind::fapp(randInt, args);
			      	randSanityExprs.push_back(mk<AND>(mk<GT>(randIntApp, curMaxGT), mk<LEQ>(randIntApp, curMinLE)));
		  	  		return randIntApp;
	          	} else { 
	            	ExprVector realArgs;
		            Expr randNameReal = mkTerm ("_aeval_tmp_rand_real_" + ind, efac);
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            Expr randReal = bind::fdecl(randNameReal, realArgs);

		      		ExprVector args;
	      			args.push_back(mk<FALSE>(efac));
	      			args.push_back(mk<TRUE>(efac));
	  				args.push_back(curMaxGT);
			      	args.push_back(curMinLE);
			  		Expr randRealApp = bind::fapp(randReal, args);
			      	randSanityExprs.push_back(mk<AND>(mk<GT>(randRealApp, curMaxGT), mk<LEQ>(randRealApp, curMinLE)));
		  	  		return randRealApp;
          		}
          	} else {
	            if (isInt)
              		return mk<IDIV>(mk<PLUS>(curMinLE, curMaxGT), mkTerm (mpz_class (2), efac));
            	else
              		return mk<DIV>(mk<PLUS>(curMinLE, curMaxGT), mkTerm (mpq_class (2), efac));
          	}
          }

          if (curMinLT != NULL && curMinLE == NULL && curMaxGT == NULL && curMaxGE != NULL)
          {

            if (nondet) {
            	string ind = lexical_cast<string> (fresh_var_ind++);
	            if (isInt) {
		            ExprVector intArgs;
		            Expr randNameInt = mkTerm ("_aeval_tmp_rand_int_" + ind, efac); 
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            Expr randInt = bind::fdecl(randNameInt, intArgs);

		      		ExprVector args;
	      			args.push_back(mk<TRUE>(efac));
	      			args.push_back(mk<FALSE>(efac));
	  				args.push_back(curMaxGE);
			      	args.push_back(curMinLT);
			  		Expr randIntApp = bind::fapp(randInt, args);
			      	randSanityExprs.push_back(mk<AND>(mk<GEQ>(randIntApp, curMaxGE), mk<LT>(randIntApp, curMinLT)));
		  	  		return randIntApp;
	          	} else {
		            ExprVector realArgs;
		            Expr randNameReal = mkTerm ("_aeval_tmp_rand_real_" + ind, efac);
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            Expr randReal = bind::fdecl(randNameReal, realArgs);

		      		ExprVector args;
	      			args.push_back(mk<TRUE>(efac));
	      			args.push_back(mk<FALSE>(efac));
	  				args.push_back(curMaxGE);
			      	args.push_back(curMinLT);
			  		Expr randRealApp = bind::fapp(randReal, args);
			      	randSanityExprs.push_back(mk<AND>(mk<GEQ>(randRealApp, curMaxGE), mk<LT>(randRealApp, curMinLT)));
		  	  		return randRealApp;
	          	}
	          } else {
	          		if (isInt)
              			return mk<IDIV>(mk<PLUS>(curMinLT, curMaxGE), mkTerm (mpz_class (2), efac));
            		else
              			return mk<DIV>(mk<PLUS>(curMinLT, curMaxGE), mkTerm (mpq_class (2), efac));
	          }
          }

          if (curMinLT != NULL && curMinLE == NULL && curMaxGT != NULL && curMaxGE != NULL)
          {

            if (nondet) {
	            string ind = lexical_cast<string> (fresh_var_ind++);
	            if (isInt) {
		            ExprVector intArgs;
		            Expr randNameInt = mkTerm ("_aeval_tmp_rand_int_" + ind, efac); 
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            Expr randInt = bind::fdecl(randNameInt, intArgs);

		      		ExprVector args;
	      			args.push_back(mk<GT>(curMaxGE, curMaxGT));
	      			args.push_back(mk<FALSE>(efac));
	  				args.push_back(curMax);
			      	args.push_back(curMinLT);
			  		Expr randIntApp = bind::fapp(randInt, args);
			      	randSanityExprs.push_back(mk<AND>(mk<ITE>(mk<GT>(curMaxGE, curMaxGT), mk<GEQ>(randIntApp, curMax),
			      		mk<GT>(randIntApp, curMax)), mk<LT>(randIntApp, curMinLT)));
		  	  		return randIntApp;
	          	} else {
		            ExprVector realArgs;
		            Expr randNameReal = mkTerm ("_aeval_tmp_rand_real_" + ind, efac);
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            Expr randReal = bind::fdecl(randNameReal, realArgs);

		      		ExprVector args;
	      			args.push_back(mk<GT>(curMaxGE, curMaxGT));
	      			args.push_back(mk<FALSE>(efac));
	  				args.push_back(curMax);
			      	args.push_back(curMinLT);
			  		Expr randRealApp = bind::fapp(randReal, args);
			      	randSanityExprs.push_back(mk<AND>(mk<ITE>(mk<GT>(curMaxGE, curMaxGT), mk<GEQ>(randRealApp, curMax),
			      		mk<GT>(randRealApp, curMax)), mk<LT>(randRealApp, curMinLT)));
		  	  		return randRealApp;
	          	}
	          } else {
      	            if (isInt)
              			return mk<IDIV>(mk<PLUS>(curMinLT, curMax), mkTerm (mpz_class (2), efac));
            		else
              			return mk<DIV>(mk<PLUS>(curMinLT, curMax), mkTerm (mpq_class (2), efac));
	          }
          }

          if (curMinLT == NULL && curMinLE != NULL && curMaxGT != NULL && curMaxGE != NULL)
          {
            if (nondet) { 
	            string ind = lexical_cast<string> (fresh_var_ind++);

	            if (isInt) {
		            ExprVector intArgs;
		            Expr randNameInt = mkTerm ("_aeval_tmp_rand_int_" + ind, efac); 
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            Expr randInt = bind::fdecl(randNameInt, intArgs);

		      		ExprVector args;
	      			args.push_back(mk<GT>(curMaxGE, curMaxGT));
	      			args.push_back(mk<TRUE>(efac));
	  				args.push_back(curMax);
			      	args.push_back(curMinLE);
			  		Expr randIntApp = bind::fapp(randInt, args);
			      	randSanityExprs.push_back(mk<AND>(mk<ITE>(mk<GT>(curMaxGE, curMaxGT), mk<GEQ>(randIntApp, curMax),
			      		mk<GT>(randIntApp, curMax)), mk<LEQ>(randIntApp, curMinLE)));
		  	  		return randIntApp;
	          	} else {
		            ExprVector realArgs;
		            Expr randNameReal = mkTerm ("_aeval_tmp_rand_real_" + ind, efac);
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            Expr randReal = bind::fdecl(randNameReal, realArgs);

		      		ExprVector args;
	      			args.push_back(mk<GT>(curMaxGE, curMaxGT));
	      			args.push_back(mk<TRUE>(efac));
	  				args.push_back(curMax);
			      	args.push_back(curMinLE);
			  		Expr randRealApp = bind::fapp(randReal, args);
			      	randSanityExprs.push_back(mk<AND>(
			      		mk<ITE>(mk<GT>(curMaxGE, curMaxGT), mk<GEQ>(randRealApp, curMax), mk<GT>(randRealApp, curMax)),
			      		mk<LEQ>(randRealApp, curMinLE)));
		  	  		return randRealApp;
	          	}
          } else {
          		if (isInt)
          			return mk<IDIV>(mk<PLUS>(curMinLE, curMax), mkTerm (mpz_class (2), efac));
        		else
	          		return mk<DIV>(mk<PLUS>(curMinLE, curMax), mkTerm (mpq_class (2), efac));
      		}
          }

          if (curMinLT != NULL && curMinLE != NULL && curMaxGT == NULL && curMaxGE != NULL)
          {
            if (nondet) { 
	            string ind = lexical_cast<string> (fresh_var_ind++);

	            if (isInt) {
		            ExprVector intArgs;
		            Expr randNameInt = mkTerm ("_aeval_tmp_rand_int_" + ind, efac); 
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            Expr randInt = bind::fdecl(randNameInt, intArgs);

		      		ExprVector args;
	      			args.push_back(mk<TRUE>(efac));
	      			args.push_back(mk<LT>(curMinLE, curMinLT));
	  				args.push_back(curMaxGE);
			      	args.push_back(curMin);
			  		Expr randIntApp = bind::fapp(randInt, args);
			      	randSanityExprs.push_back(mk<AND>(mk<GEQ>(randIntApp, curMaxGE),
			      		mk<ITE>(mk<LT>(curMinLE, curMinLT), mk<LEQ>(randIntApp, curMin), mk<LT>(randIntApp, curMin))));
		  	  		return randIntApp;
	          	} else {
		            ExprVector realArgs;
		            Expr randNameReal = mkTerm ("_aeval_tmp_rand_real_" + ind, efac);
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            Expr randReal = bind::fdecl(randNameReal, realArgs);

		      		ExprVector args;
	      			args.push_back(mk<TRUE>(efac));
	      			args.push_back(mk<LT>(curMinLE, curMinLT));
	  				args.push_back(curMaxGE);
			      	args.push_back(curMin);
			  		Expr randRealApp = bind::fapp(randReal, args);
			      	randSanityExprs.push_back(mk<AND>(mk<GEQ>(randRealApp, curMaxGE),
	              		mk<ITE>(mk<LT>(curMinLE, curMinLT), mk<LEQ>(randRealApp, curMin), mk<LT>(randRealApp, curMin))));
		  	  		return randRealApp;
	          	}
          	} else {
          		if (isInt)
              		return mk<IDIV>(mk<PLUS>(curMin, curMaxGE), mkTerm (mpz_class (2), efac));
            	else
              		return mk<DIV>(mk<PLUS>(curMin, curMaxGE), mkTerm (mpq_class (2), efac));
          	}
          }

          if (curMinLT != NULL && curMinLE != NULL && curMaxGT != NULL && curMaxGE == NULL)
          {
            if (nondet) {
	            string ind = lexical_cast<string> (fresh_var_ind++);
	            if (isInt) {
		            ExprVector intArgs;
		            Expr randNameInt = mkTerm ("_aeval_tmp_rand_int_" + ind, efac); 
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            Expr randInt = bind::fdecl(randNameInt, intArgs);

		      		ExprVector args;
	      			args.push_back(mk<FALSE>(efac));
	      			args.push_back(mk<LT>(curMinLE, curMinLT));
	  				args.push_back(curMaxGT);
			      	args.push_back(curMin);
			  		Expr randIntApp = bind::fapp(randInt, args);
			      	randSanityExprs.push_back(mk<AND>(mk<GT>(randIntApp, curMaxGT),
			      		mk<ITE>(mk<LT>(curMinLE, curMinLT), mk<LEQ>(randIntApp, curMin), mk<LT>(randIntApp, curMin))));
		  	  		return randIntApp;
	          	}

	            else {
		            ExprVector realArgs;
		            Expr randNameReal = mkTerm ("_aeval_tmp_rand_real_" + ind, efac);
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            Expr randReal = bind::fdecl(randNameReal, realArgs);

		      		ExprVector args;
	      			args.push_back(mk<FALSE>(efac));
	      			args.push_back(mk<LT>(curMinLE, curMinLT));
	  				args.push_back(curMaxGT);
			      	args.push_back(curMin);
			  		Expr randRealApp = bind::fapp(randReal, args);
			      	randSanityExprs.push_back(mk<AND>(mk<GT>(randRealApp, curMaxGT),
			      		mk<ITE>(mk<LT>(curMinLE, curMinLT), mk<LEQ>(randRealApp, curMin), mk<LT>(randRealApp, curMin))));
		  	  		return randRealApp;
	          	}
	        } else {
	        	if (isInt)
              		return mk<IDIV>(mk<PLUS>(curMin, curMaxGT), mkTerm (mpz_class (2), efac));
            	else
              		return mk<DIV>(mk<PLUS>(curMin, curMaxGT), mkTerm (mpq_class (2), efac));
	        }
          }

          if (curMinLT != NULL && curMinLE != NULL && curMaxGT != NULL && curMaxGE != NULL)
          {
            if (nondet) { 
	            string ind = lexical_cast<string> (fresh_var_ind++);
	            if (isInt) {
		            ExprVector intArgs;
		            Expr randNameInt = mkTerm ("_aeval_tmp_rand_int_" + ind, efac); 
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::boolTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            intArgs.push_back(sort::intTy (efac));
		            Expr randInt = bind::fdecl(randNameInt, intArgs);

		      		ExprVector args;
	      			args.push_back(mk<GT>(curMaxGE, curMaxGT));
	      			args.push_back(mk<LT>(curMinLE, curMinLT));
	  				args.push_back(curMax);
			      	args.push_back(curMin);
			  		Expr randIntApp = bind::fapp(randInt, args);
			      	randSanityExprs.push_back(mk<AND>(
			      		mk<ITE>(mk<GT>(curMaxGE, curMaxGT), mk<GEQ>(randIntApp, curMax), mk<GT>(randIntApp, curMax)), 
			      		mk<ITE>(mk<LT>(curMinLE, curMinLT), mk<LEQ>(randIntApp, curMin), mk<LT>(randIntApp, curMin))));
		  	  		return randIntApp;
	          	}

	            else {
		            ExprVector realArgs;
		            Expr randNameReal = mkTerm ("_aeval_tmp_rand_real_" + ind, efac);
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::boolTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            realArgs.push_back(sort::realTy (efac));
		            Expr randReal = bind::fdecl(randNameReal, realArgs);

		      		ExprVector args;
	      			args.push_back(mk<GT>(curMaxGE, curMaxGT));
	      			args.push_back(mk<LT>(curMinLE, curMinLT));
	  				args.push_back(curMax);
			      	args.push_back(curMin);
			  		Expr randRealApp = bind::fapp(randReal, args);
			      	randSanityExprs.push_back(mk<AND>(
			      		mk<ITE>(mk<GT>(curMaxGE, curMaxGT), mk<GEQ>(randRealApp, curMax), mk<GT>(randRealApp, curMax)), 
			      		mk<ITE>(mk<LT>(curMinLE, curMinLT), mk<LEQ>(randRealApp, curMin), mk<LT>(randRealApp, curMin))));
		  	  		return randRealApp;
	          	}
	        } else {
            	if (isInt)
              		return mk<IDIV>(mk<PLUS>(curMin, curMax), mkTerm (mpz_class (2), efac));
            	else
              		return mk<DIV>(mk<PLUS>(curMin, curMax), mkTerm (mpq_class (2), efac));
	        }
          }

          // Andreas : The if blocks below assign the closed bound, preventing the use of random values
          // Andreas : These were the first checks in this block.
          if (curMinLT == NULL && curMinLE != NULL)
          {
            if (nondet) {
              return minusEps(curMinLE, isInt, true);
            } else {
              return curMinLE;
            }
          }

          if (curMaxGT == NULL && curMaxGE != NULL)
          {
            if (nondet) {
              return plusEps(curMaxGE, isInt, true);
            } else {
              return curMaxGE;
            }
          }

          assert(0);
        }

        // here conjNEQ.size() > 0

        Expr tmpMin;
        GetSymbolicMin(conjNEQ, tmpMin, isInt);
        Expr tmpMax;
        GetSymbolicMax(conjNEQ, tmpMax, isInt);
        if (curMinLE == NULL && curMinLT == NULL && curMaxGE == NULL && curMaxGT == NULL)
        {
          return plusEps(tmpMax, isInt, false);
        }

        if (curMinLE != NULL && curMinLT == NULL && curMaxGE == NULL && curMaxGT == NULL)
        {
          return minusEps(mk<ITE>(mk<LT>(curMinLE, tmpMin), curMinLE, tmpMin), isInt, false);
        }

        if (curMinLE == NULL && curMinLT != NULL && curMaxGE == NULL && curMaxGT == NULL)
        {
          return minusEps(mk<ITE>(mk<LT>(curMinLT, tmpMin), curMinLT, tmpMin), isInt, false);
        }

        if (curMinLE != NULL && curMinLT != NULL && curMaxGE == NULL && curMaxGT == NULL)
        {
          return minusEps(mk<ITE>(mk<LT>(curMin, tmpMin), curMin, tmpMin), isInt, false);
        }

        if (curMinLE == NULL && curMinLT == NULL && curMaxGE != NULL && curMaxGT == NULL)
        {
          return plusEps(mk<ITE>(mk<GT>(curMaxGE, tmpMax), curMaxGE, tmpMax), isInt, false);
        }

        if (curMinLE == NULL && curMinLT == NULL && curMaxGE == NULL && curMaxGT != NULL)
        {
          return plusEps(mk<ITE>(mk<GT>(curMaxGT, tmpMax), curMaxGT, tmpMax), isInt, false);
        }

        if (curMinLE == NULL && curMinLT == NULL && curMaxGE != NULL && curMaxGT != NULL)
        {
          return plusEps(mk<ITE>(mk<GT>(curMax, tmpMax), curMax, tmpMax), isInt, false);
        }

        assert (curMinLE != NULL || curMinLT != NULL);
        assert (curMaxGE != NULL || curMaxGT != NULL);

        Expr curMid;
        if (nondet) {
	        Expr lflag;
	        Expr uflag;
	        if (curMaxGE == NULL && curMaxGT != NULL) {
	          // curMax = mk<ITE>(mk<GT>(curMaxGT, tmpMax), curMaxGT, tmpMax);
	          curMax = curMaxGT;
	          lflag = mk<FALSE>(efac);
	        } 
	        else if (curMaxGE != NULL && curMaxGT == NULL) {
	          curMax = curMaxGE;
	          // curMax = mk<ITE>(mk<GT>(curMaxGE, tmpMax), curMaxGT, tmpMax);
	          lflag = mk<TRUE>(efac);
	        }

	        if (curMinLE == NULL && curMinLT != NULL) {
	          curMin = curMinLT;
	          // curMin = mk<ITE>(mk<LT>(curMin, tmpMin), curMin, tmpMin);
	          uflag = mk<FALSE>(efac);
	        }
	        else if (curMinLE != NULL && curMinLT == NULL) {
	          curMin = curMinLE;
	          // curMin = mk<ITE>(mk<LT>(curMin, tmpMin), curMin, tmpMin);
	          uflag = mk<TRUE>(efac);
	        }

	        if (curMaxGE != NULL && curMaxGT != NULL) {
	          // curMax = mk<ITE>(mk<GT>(curMaxGT, curMaxGE), 
	            // mk<ITE>(mk<GT>(curMaxGT, tmpMax), curMaxGT, tmpMax),
	            // mk<ITE>(mk<GT>(curMaxGE, tmpMax), curMaxGE ,tmpMax));
	          curMax = mk<ITE>(mk<GT>(curMaxGT, curMaxGE), curMaxGT, curMaxGE);
	          lflag = mk<GT>(curMaxGE, curMaxGT);
	        }

	        if (curMinLT != NULL && curMinLE != NULL) {
	          // curMin = mk<ITE>(mk<LT>(curMinLT, curMinLE),
	            // mk<ITE>(mk<LT>(curMinLT, tmpMin), curMinLT, tmpMin),
	            // mk<ITE>(mk<LT>(curMinLE, tmpMin), curMinLE, tmpMin));
	          // curMin = mk<ITE>(mk<LT>(curMinLT, curMinLE), curMinLT, curMinLE);
	          uflag = mk<LT>(curMinLE, curMinLT);
	        }
            // GetSymbolicNeqNonDet(conjNEQ, curMax, curMin, curMid, (curMaxGE == NULL), (curMinLE == NULL), isInt);
        	GetSymbolicNeqNonDet(conjNEQ, curMax, curMin, curMid, lflag, uflag, isInt);
        } else {

        	if (curMaxGE == NULL) curMax = curMaxGT;
        	else curMax = curMaxGE;

        	if (curMinLE == NULL) curMin = curMinLT;
        	else curMin = curMinLE;
	        GetSymbolicNeq(conjNEQ, curMax, curMin, curMid, (curMaxGE == NULL), isInt);
    	}
        return curMid;
      }
      return exp;
    }

    void searchDownwards(set<int> &indexes, Expr var, ExprVector& skol)
    {
      if (debug)
      {
        outs () << "searchDownwards for " << *var << ": [[ indexes: ";
        for (auto i : indexes) outs() << i << ", ";
        outs () << " ]]\n";
      }
      if (indexes.empty()) return;

      ExprSet quant;
      quant.insert(var);
      ExprSet pre;
      ExprSet post;
      for (auto i : indexes)
      {
        pre.insert(projections[i]);
        post.insert(skol[i]);
      }
      AeValSolver ae(disjoin(pre, efac), conjoin(post, efac), quant, false, false, nondet);

      if (!ae.solve())
      {
        if (bestIndexes.size() < indexes.size()) bestIndexes = indexes;
        return;
      }
      else
      {
        Expr subs = ae.getValidSubset();
        if (isOpX<FALSE>(subs))
        {
//          for (int j : indexes)
//          {
//            set<int> indexes2 = indexes;
//            indexes2.erase(j);
//            searchDownwards(indexes2, var, skol);
//          }
          return;
        }
        else
        {
          bool erased = false;

          for (auto i = indexes.begin(); i != indexes.end();)
          {
            if (!u.implies(subs, projections[*i]))
            {
              i = indexes.erase(i);
              erased = true;
            }
            else
            {
              ++i;
            }
          }
          if (erased)
          {
            searchDownwards(indexes, var, skol);
          }
          else
          {
            for (int j : indexes)
            {
              set<int> indexes2 = indexes;
              indexes2.erase(j);
              searchDownwards(indexes2, var, skol);
            }
          }
        }
      }
    }

    void searchUpwards(set<int> &indexes, Expr var, ExprVector& skol)
    {
      if (debug)
      {
        outs () << "searchUpwards for " << *var << ": [[ indexes: ";
        for (auto i : indexes) outs() << i << ", ";
        outs () << " ]]\n";
      }
      ExprSet quant;
      quant.insert(var);
      ExprSet pre;
      ExprSet post;
      for (auto i : indexes)
      {
        pre.insert(projections[i]);
        post.insert(skol[i]);
      }
      AeValSolver ae(disjoin(pre, efac), conjoin(post, efac), quant, false, false, nondet);

      if (!ae.solve())
      {
        if (bestIndexes.size() < indexes.size()) bestIndexes = indexes;
        for (int i = 0; i < partitioning_size; i++)
        {
          if (find (indexes.begin(), indexes.end(), i) != indexes.end()) continue;
          set<int> indexes2 = indexes;
          indexes2.insert(i);
          searchUpwards(indexes2, var, skol);
        }
        return;
      }
    }

    void breakCyclicSubsts(ExprMap& cyclicSubsts, ExprMap& evals, ExprMap& substsMap)
    {
      if (cyclicSubsts.empty()) return;

      map<Expr, int> tmp;
      for (auto & a : cyclicSubsts)
      {
        ExprSet vars;
        filter (a.second, bind::IsConst (), inserter (vars, vars.begin()));
        for (auto & b : vars)
        {
          if (find(v.begin(), v.end(), b) != v.end())
            tmp[b]++;
        }
      }

      int min = 0;
      Expr a;
      for (auto & b : tmp)
      {
        if (b.second >= min)
        {
          min = b.second;
          a = b.first;
        }
      }

      for (auto b = cyclicSubsts.begin(); b != cyclicSubsts.end(); b++)
        if (b->first == a)
        {
          substsMap[a] = evals[a]->right();
          cyclicSubsts.erase(b); break;
        }

      substsMap.insert (cyclicSubsts.begin(), cyclicSubsts.end());
      splitDefs(substsMap, cyclicSubsts);
      breakCyclicSubsts(cyclicSubsts, evals, substsMap);
    }

    Expr combineAssignments(ExprMap& allAssms, ExprMap& evals)
    {
      ExprSet skolTmp;
      ExprMap cyclicSubsts;
      splitDefs(allAssms, cyclicSubsts);

      breakCyclicSubsts(cyclicSubsts, evals, allAssms);
      assert (cyclicSubsts.empty());
      for (auto & a : sensitiveVars)
      {
        assert (emptyIntersect(allAssms[a], v));
        skolTmp.insert(mk<EQ>(a, allAssms[a]));
      }
      return conjoin(skolTmp, efac);
    }

    Expr getSkolemFunction (bool compact = false)
    {
      ExprSet skolUncond;
      ExprSet eligibleVars;

      skolemConstraints.clear(); // GF: just in case
      for (auto &var: v)
      {
        bool elig = compact;
        for (int i = 0; i < partitioning_size; i++)
        {
          if (defMap[var] != NULL)
          {
            skolMaps[i][var] = mk<EQ>(var, defMap[var]);
          }
          else if (skolMaps[i][var] == NULL)
          {
            ExprSet pre;
            pre.insert(skolSkope);
            for (auto & a : skolMaps[i]) if (a.second != NULL) pre.insert(a.second);
            pre.insert(t);
            Expr assm = getCondDefinitionFormula(var, conjoin(pre, efac));
            if (assm != NULL)
            {
              skolMaps[i][var] = assm;
            }
            else if (someEvals[i][var] != NULL)
            {
              skolMaps[i][var] = someEvals[i][var];
            }
            else skolMaps[i][var] = mk<EQ>(var, getDefaultAssignment(var));
          }

          if (compact) // small optim:
          {
            if (bind::isBoolConst(var) && u.isEquiv(skolMaps[i][var]->right(), mk<TRUE>(efac)))
              skolMaps[i][var] = mk<EQ>(var, mk<TRUE>(efac));
            if (bind::isBoolConst(var) && u.isEquiv(skolMaps[i][var]->right(), mk<FALSE>(efac)))
              skolMaps[i][var] = mk<EQ>(var, mk<FALSE>(efac));
          }

          elig &= (1 == intersectSize (skolMaps[i][var], v));
        }
        if (elig) eligibleVars.insert(var);
        else sensitiveVars.insert(var);
      }

      for (auto & a : v)
      {
        ExprVector t;
        for (int i = 0; i < partitioning_size; i++)
        {
          assert(skolMaps[i][a] != NULL);
          t.push_back(skolMaps[i][a]); // should be on i-th position
        }
        skolemConstraints[a] = t;
      }

      map<Expr, set<int>> inds;
      ExprMap sameAssms;
      for (auto & var : eligibleVars)
      {
        bool same = true;
        auto & a = skolemConstraints[var];
        for (int i = 1; i < partitioning_size; i++)
        {
          if (a[0] != a[i])
          {
            same = false;
            break;
          }
        }
        if (same)
        {
          sameAssms[var] = getAssignmentForVar(var, a[0]);
          skolUncond.insert(mk<EQ>(var, sameAssms[var]));
        }
        else
        {
          sensitiveVars.insert(var);
        }
      }

      for (auto & var : sensitiveVars)
      {
        bestIndexes.clear();
        if (find(eligibleVars.begin(), eligibleVars.end(), var) != eligibleVars.end()
            && compact)
        {
          set<int> indexes;
          for (int i = 0; i < partitioning_size; i++) indexes.insert(i);
          searchDownwards (indexes, var, skolemConstraints[var]);
          searchUpwards (bestIndexes, var, skolemConstraints[var]);
        }
        inds[var] = bestIndexes;
      }

      Expr skol;
      ExprSet skolTmp;
      if (sensitiveVars.size() > 0)
      {
        set<int> intersect;
        for (int i = 0; i < partitioning_size; i ++)
        {
          int found = true;
          for (auto & a : inds)
          {
            if (find (a.second.begin(), a.second.end(), i) == a.second.end())
            {
              found = false;
              break;
            }
          }
          if (found) intersect.insert(i);
        }

        if (intersect.size() <= 1)
        {
          int maxSz = 0;
          int largestPre = 0;
          for (int i = 0; i < partitioning_size; i++)
          {
            int curSz = treeSize(projections[i]);
            if (curSz > maxSz)
            {
              maxSz = curSz;
              largestPre = i;
            }
          }
          intersect.clear();
          intersect.insert(largestPre);
        }

        ExprMap allAssms = sameAssms;
        for (auto & a : sensitiveVars)
        {
          ExprSet cnjs;
          for (int b : intersect) getConj(skolemConstraints[a][b], cnjs);
          Expr def = getAssignmentForVar(a, conjoin(cnjs, efac));
          allAssms[a] = def;
        }
        Expr bigSkol = combineAssignments(allAssms, someEvals[*intersect.begin()]);

        for (int i = 0; i < partitioning_size; i++)
        {
          allAssms = sameAssms;
          if (find(intersect.begin(), intersect.end(), i) == intersect.end())
          {
            for (auto & a : sensitiveVars)
            {
              Expr def = getAssignmentForVar(a, skolemConstraints[a][i]);
              allAssms[a] = def;
            }
            bigSkol = mk<ITE>(projections[i], combineAssignments(allAssms, someEvals[i]), bigSkol);
            if (compact) bigSkol = u.simplifyITE(bigSkol);
          }
        }
        skolUncond.insert(bigSkol);
      }

      skol = mk<AND>(skolSkope, conjoin(skolUncond, efac));
      if (nondet && debug) {
	      Expr randSanityExpr = mk<TRUE>(efac);
	      for (auto &var : randSanityExprs){
			    bool isInt = bind::isIntConst(var);
	  		  randSanityExpr = mk<AND>(randSanityExpr, var);
	  	  }

	      outs() << "Sanity check: " << u.implies(mk<AND>(randSanityExpr, mk<AND>(s, skol)), t) << "\n";
      } else {
      	  if (debug) outs () << "Sanity check: " << u.implies(mk<AND>(s, skol), t) << "\n";
      }

      return skol;
    }

    int getPartitioningSize()
    {
      return partitioning_size;
    }

    // Runnable only after getSkolemFunction
    Expr getSkolemConstraints(int i)
    {
      ExprSet constrs;
      for (auto & a : skolemConstraints)
        constrs.insert(a.second[i]);
      return conjoin(constrs, efac);
    }

    /**
     * Actually, just print it to cmd in the smt-lib2 format
     */
    void serialize_formula(Expr form)
    {
      smt.reset();
      smt.assertExpr(form);
      smt.toSmtLib (outs());
      outs().flush ();
    }

    ExprVector getRandSanityExprs()
    {
      return randSanityExprs;
    }

  };

  /**
   * Simple wrapper
   */
  inline void aeSolveAndSkolemize(Expr s, Expr t, bool skol, bool debug, bool compact, bool nondet)
  {
    ExprSet s_vars;
    ExprSet t_vars;

    filter (s, bind::IsConst (), inserter (s_vars, s_vars.begin()));
    filter (t, bind::IsConst (), inserter (t_vars, t_vars.begin()));

    ExprSet t_quantified = minusSets(t_vars, s_vars);

    s = convertIntsToReals<DIV>(s);
    t = convertIntsToReals<DIV>(t);

    if (debug)
    {
      outs() << "S: " << *s << "\n";
      outs() << "T: \\exists ";
      for (auto &a: t_quantified) outs() << *a << ", ";
      outs() << *t << "\n";
    }

    AeValSolver ae(s, t, t_quantified, debug, skol, nondet);

    if (ae.solve()){
      outs () << "Iter: " << ae.getPartitioningSize() << "; Result: invalid\n";
      ae.printModelNeg();
      outs() << "\nvalid subset:\n";
      ae.serialize_formula(ae.getValidSubset());
    } else {
      outs () << "Iter: " << ae.getPartitioningSize() << "; Result: valid\n";
      if (skol)
      {
        outs() << "\nextracted skolem:\n";
        Expr skol = ae.getSkolemFunction(compact);
        ae.serialize_formula(skol);
      }
    }
  }

  inline void getAllInclusiveSkolem(Expr s, Expr t, bool debug, bool compact, bool nondet)
  {
    ExprSet s_vars;
    ExprSet t_vars;

    filter (s, bind::IsConst (), inserter (s_vars, s_vars.begin()));
    filter (t, bind::IsConst (), inserter (t_vars, t_vars.begin()));

    ExprSet t_quantified = minusSets(t_vars, s_vars);

    s = convertIntsToReals<DIV>(s);
    t = convertIntsToReals<DIV>(t);

    SMTUtils u(s->getFactory());

    if (debug)
    {
      outs() << "S: " << *s << "\n";
      outs() << "T: \\exists ";
      for (auto &a: t_quantified) outs() << *a << ", ";
      outs() << *t << "\n";
    }

    Expr t_init = t;
    ExprVector skolems;

    //Andreas
    Expr randSanityExpr = mk<TRUE>(s->getFactory());
    
    while (true)
    {
      AeValSolver ae(s, t, t_quantified, debug, true, nondet);

      if (ae.solve()){
        if (skolems.size() == 0)
        {
          outs () << "Result: invalid\n";
          ae.printModelNeg();
          outs() << "\nvalid subset:\n";
          u.serialize_formula(ae.getValidSubset());
          return;
        }
        break;
      } else {
        skolems.push_back(ae.getSkolemFunction(compact));
        t = mk<AND>(t, mk<NEG>(ae.getSkolemConstraints(0)));
        //Andreas
        if (nondet) {
        	ExprVector randSanityExprs = ae.getRandSanityExprs();
        	for (auto &var : randSanityExprs){
          		bool isInt = bind::isIntConst(var);
          		randSanityExpr = mk<AND>(randSanityExpr, var);
        	}
      	}
      }
    }

    Expr skol = skolems.back();
    if (skolems.size() > 1)
    {
      Expr varName = mkTerm <std::string> ("_aeval_tmp_rnd", s->getFactory());
      Expr var = bind::intConst(varName);
      for (int i = skolems.size() - 2; i >= 0; i--)
      {
        skol = mk<ITE>(mk<EQ>(var, mkTerm (mpz_class (i), s->getFactory())),
                       skolems[i], skol);
      }
    }

    

    if (nondet && debug) {
      outs() << "Sanity check [all-inclusive]: " << u.implies(mk<AND>
                  (randSanityExpr, mk<AND>(s, skol)), t_init) << "\n";
    } else {
    	if (debug) outs () << "Sanity check [all-inclusive]: " << 
    		u.implies(mk<AND>(s, skol), t_init) << "\n";
    }


    outs () << "Result: valid\n\nextracted skolem:\n";
    u.serialize_formula(skol);
  };
}

#endif
