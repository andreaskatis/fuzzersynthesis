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
    ExprSet v; // existentially quantified vars
    ExprVector stVars;
    
    ExprSet tConjs;
    ExprSet usedConjs;
    ExprMap defMap;
    ExprSet conflictVars;
    
    ExprFactory &efac;
    EZ3 z3;
    ZSolver<EZ3> smt;
    SMTUtils u;
    
    unsigned partitioning_size;
    ExprVector projections;
    ExprVector instantiations;
    ExprVector interpolants;
    vector<ExprMap> skolMaps;
    vector<ExprMap> someEvals;
    Expr skolSkope;
    
    bool debug;
    unsigned fresh_var_ind;
    
  public:
    
    AeValSolver (Expr _s, Expr _t, ExprSet &_v) :
    s(_s), t(_t), v(_v),
    efac(s->getFactory()),
    z3(efac),
    smt (z3),
    u(efac),
    fresh_var_ind(0),
    partitioning_size(0),
    debug(0)
    {
      filter (boolop::land(s,t), bind::IsConst (), back_inserter (stVars));
      getConj(t, tConjs);
      for (auto &exp: v) {
        Expr definition = getDefinitionFormulaFromT(exp);
        if (definition != NULL) defMap[exp] = u.simplifyITE(definition);
      }
    }
    
    /**
     * Decide validity of \forall s => \exists v . t
     */
    boost::tribool solve ()
    {
      smt.reset();
      smt.assertExpr (s);
      if (!smt.solve ()) {
        outs() << "\nE.v.: -; Iter.: 0; Result: valid\n\n";
        return false;
      }
      if (v.size () == 0)
      {
        smt.assertExpr (boolop::lneg (t));
        boost::tribool res = smt.solve ();
        outs() << "\nE.v.: 0; Iter.: 0; Result: " << (res? "invalid" : "valid") << "\n\n";
        return res;
      }
      
      smt.push ();
      smt.assertExpr (t);
      
      boost::tribool res = true;
      
      while (smt.solve ())
      {
        outs() << ".";
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

        getMBPandSkolem(m);

        smt.pop();
        smt.assertExpr(boolop::lneg(projections[partitioning_size++]));
        if (!smt.solve()) { res = false; break; }

        smt.push();
        smt.assertExpr (t);
      }
      
      outs() << "\nE.v.: " << v.size() << "; Iter.: " << partitioning_size
             << "; Result: " << (res? "invalid" : "valid") << "\n\n";
      
      return res;
    }
    
    /**
     * Extract MBP and local Skolem
     */
    void getMBPandSkolem(ZSolver<EZ3>::Model &m)
    {
      Expr pr = t;
      ExprMap substsMap;
      ExprMap modelMap;
      for (auto &exp: v)
      {
        ExprMap map;
        pr = z3_qe_model_project_skolem (z3, m, exp, pr, map);
        getLocalSkolems(m, exp, map, substsMap, modelMap, pr);
      }
      
      if (debug) assert(emptyIntersect(pr, v));

      someEvals.push_back(modelMap);
      skolMaps.push_back(substsMap);
      projections.push_back(pr);
    }
    
    /**
     * Compute local skolems based on the model
     */
    void getLocalSkolems(ZSolver<EZ3>::Model &m, Expr exp,
                         ExprMap &map, ExprMap &substsMap, ExprMap &modelMap, Expr& mbp)
    {
      if (map.size() > 0){
        ExprSet substs;
        for (auto &e: map){
          Expr ef = e.first;
          Expr es = e.second;

          if (debug) outs() << "subst: " << *ef << "  <-->  " << *es << "\n";

          if (isOpX<TRUE>(es)){
            substs.insert(ineqNegReverter(ef));
          } else if (isOpX<FALSE>(es)){
            if (isOpX<NEG>(ef)){
              ef = ef->arg(0);
            } else {
              ef = ineqNegReverter(mk<NEG>(ef));
            }
            substs.insert(ef);
          } else if (es == mbp) {
            substs.insert(ineqNegReverter(ef));
          } else if (!(isOp<BoolOp>(ef) && isOp<BoolOp>(es)) &&
                     !(isOp<ComparissonOp>(ef) && isOp<ComparissonOp>(es)) &&
                     !(isOp<BoolOp>(ef) && isOp<ComparissonOp>(es)) &&
                     !(isOp<ComparissonOp>(ef) && isOp<BoolOp>(es))){
            substs.insert(mk<EQ>(ineqNegReverter(ef), ineqNegReverter(es)));
          } else {
            Expr mergedSides = mergeIneqs(ef, es);
            if (mergedSides != NULL) {
              substs.insert(mergedSides);
            }
          }
        }
        if (substs.size() == 0) outs() << "WARNING: subst is empty for " << *exp << "\n";
        substsMap[exp] = conjoin(substs, efac);

      } else if (m.eval(exp) != exp){
        if (debug) outs () << "model: " << *exp <<  "  <-->  " << *m.eval(exp) << "\n";
        modelMap[exp] = mk<EQ>(exp, m.eval(exp));
      }
    }
    
    /**
     * tmp
     */
    
    void fillTmpDef(ExprMap& eval, bool pos, Expr def, ExprMap& tmpDefMap){

      if (isOpX<EQ>(def)){

        Expr l = def->left();
        Expr r = def->right();

        bool hl = find(std::begin(v), std::end (v), l) != std::end(v);
        bool hr = find(std::begin(v), std::end (v), r) != std::end(v);

        if (pos){

          if (hl && (bind::isBoolConst(l) || bind::isIntConst(l) || bind::isRealConst(l))){
            tmpDefMap[l] = r;
          }
          if (hr && (bind::isBoolConst(r) || bind::isIntConst(r) || bind::isRealConst(r))){
            tmpDefMap[r] = l;
          }
          if (hl && isOpX<NEG>(l) && bind::isBoolConst(l->left())){
            tmpDefMap[l->left()] = mk<NEG>(r);
          }
          if (hr && isOpX<NEG>(r) && bind::isBoolConst(r->left())){
            tmpDefMap[r->left()] = mk<NEG>(l);
          }

        } else {

          if (hl && bind::isBoolConst(l)){
            tmpDefMap[l] = mk<NEG>(r);
          }
          if (hr && bind::isBoolConst(r)){
            tmpDefMap[r] = mk<NEG>(l);
          }
          if (hl && isOpX<NEG>(l) && bind::isBoolConst(l->left())){
            tmpDefMap[l->left()] = r;
          }
          if (hr && isOpX<NEG>(r) && bind::isBoolConst(r->left())){
            tmpDefMap[r->left()] = l;
          }
        }

      } else if (isOpX<NEQ>(def)){

        if (pos) fillTmpDef(eval, !pos, mk<EQ>(def->left(), def->right()), tmpDefMap);

      } else if (isOpX<NEG>(def)){

        if (pos) fillTmpDef(eval, !pos, def->left(), tmpDefMap);

      } else if (isOpX<ITE>(def)){

        fillTmpDef(eval, pos, mk<IMPL>(def->arg(0), def->arg(1)), tmpDefMap);
        fillTmpDef(eval, pos, mk<IMPL>(mk<NEG>(def->arg(0)), def->arg(2)), tmpDefMap);

      } else if (isOpX<IMPL>(def)){

        if (pos) fillTmpDef(eval, pos, mk<OR>(mk<NEG>(def->left()), def->right()), tmpDefMap);

      } else if (isOpX<AND>(def)){

        ExprSet cnjs;
        getConj(def, cnjs);
        if (pos) for (auto &c : cnjs) fillTmpDef (eval, pos, c, tmpDefMap);

      } else if (isOpX<OR>(def)){

        ExprSet dsjs;
        getDisj(def, dsjs);
        if (!pos) for (auto &c : dsjs) fillTmpDef (eval, pos, c, tmpDefMap);

      }
      else {
        if (debug) outs() << "WARNING! unsupported: " << *def << "\n";
      }
    }

    /**
     * Global Skolem function from MBPs and local ones
     */
    Expr getSimpleSkolemFunction()
    {
      if (partitioning_size == 0){
        outs() << "WARNING: Skolem can be arbitrary\n";
        return mk<TRUE>(efac);
      }
      
      skolSkope = mk<TRUE>(efac);
      
      for (int i = 0; i < partitioning_size; i++)
      {
        ExprSet skoledvars;
        ExprMap substsMap;
        ExprMap tmpDefMap;
        ExprMap depMap;

        // do booleans first
        for (auto &exp: v) {
          if (!bind::isBoolConst(exp)) continue;

          int curSz = tmpDefMap.size();
          Expr exp2 = someEvals[i][exp];

          if (defMap[exp] != NULL && exp2 != NULL) {

            Expr def = defMap[exp];

            if (isOpX<TRUE>(exp2->right())) {
              fillTmpDef(someEvals[i], true, def, tmpDefMap);
            } else if (isOpX<FALSE>(exp2->right())) {
              fillTmpDef(someEvals[i], false, def, tmpDefMap);
            }
          }

          if (tmpDefMap.size() > curSz) defMap[exp] = exp2->right();
        }

        for (auto &exp: v) {

          Expr exp2 = skolMaps[i][exp];
          if (exp2 != NULL) { exp2 = getAssignmentForVar(exp, exp2); }
          if (exp2 == NULL) { exp2 = depMap[exp]; }
          if (exp2 == NULL) { exp2 = tmpDefMap[exp]; }
          if (exp2 == NULL) { exp2 = defMap[exp]; }

          Expr exp3 = someEvals[i][exp];
          if (exp2 == NULL && exp3 != NULL) { exp2 = exp3->right(); }
          if (exp2 == NULL) { exp2 = getDefaultAssignment(exp); }

          if (debug) outs() << "compiling skolem [pt1]: " << *exp <<  "    -->   " << *exp2 << "\n";

          substsMap[exp] = exp2;
        }

        // get rid of inter-dependencies cascadically:

        ExprVector cnjs;

        for (auto &exp: v) {
          refreshMapEntry(substsMap, exp);
          cnjs.push_back(mk<EQ>(exp, substsMap[exp]));
        }

        instantiations.push_back(conjoin(cnjs, efac));

        if (debug) outs() << "Sanity check [" << i << "]: " << u.isImplies(mk<AND>
              (mk<AND>(s, skolSkope), mk<AND> (projections[i], instantiations[i])), t) << "\n";

      }
      Expr sk = mk<TRUE>(efac);
      
      for (int i = partitioning_size - 1; i >= 0; i--){
        if (isOpX<TRUE>(projections[i]) && isOpX<TRUE>(sk)) sk = instantiations[i];
        else sk = mk<ITE>(projections[i], instantiations[i], sk);
      }
      
      Expr skol = simplifiedAnd(skolSkope, sk);
      
      if (debug) outs() << "Sanity check: " << u.isImplies(mk<AND>(s, skol), t) << "\n";
      
      return skol;
    }
    
    /**
     * Valid Subset of S (if overall AE-formula is invalid)
     */
    Expr getValidSubset()
    {
      if (partitioning_size == 0){
        outs() << "WARNING: Trivial valid subset (equal to False) due to 0 iterations\n";
      }
      return mk<AND>(s, disjoin(projections, efac));
    }
    
    /**
     * Mine the structure of T to get what was assigned to a variable
     */
    Expr getDefinitionFormulaFromT(Expr var)
    {
      Expr def;
      for (auto & cnj : tConjs)
      {
        // get equality (unique per variable)
        if (std::find(std::begin(usedConjs),
                      std::end  (usedConjs), cnj) != std::end(usedConjs)) continue;

        if (isOpX<EQ>(cnj))
        {
          if (var == cnj->left())
          {
            def = cnj->right();
            usedConjs.insert(cnj);
            break;
          }
          else if (var == cnj->right())
          {
            def = cnj->left();
            usedConjs.insert(cnj);
            break;
          }
        }
      }
      return def;
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

          skolSkope = simplifiedAnd(skolSkope,
                                    mk<EQ>(var, mk<ITE>(mk<LT>(curMax, a), a, curMax)));
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

          skolSkope = simplifiedAnd(skolSkope,
                                    mk<EQ>(var, mk<ITE>(mk<GT>(curMin, a), a, curMin)));
          curMin = var;
        }
      }
    }
    
    /**
     * Weird thing, never happens in the experiments
     */
    void GetSymbolicNeg(ExprSet& vec, Expr& lower, Expr& upper, Expr& candidate, bool isInt)
    {
      // TODO: maybe buggy in LIA, due to a naive shrinking of the segment;
      
      for (auto &a : vec){

        ExprSet forLower;
        forLower.insert(lower);
        forLower.insert(a);
        Expr updLower;
        GetSymbolicMax(forLower, updLower, isInt);

        ExprSet forUpper;
        forUpper.insert(upper);
        forUpper.insert(a);
        Expr updUpper;
        GetSymbolicMin(forUpper, updUpper, isInt);

        // TODO: do optimizations

        // first, try to see if there are any concrete values for updLower and updUpper
        if (updLower == updUpper) {
          upper = updUpper;
        }
        else if (upper != updUpper) {
          // second, force the symbolic value for upper
          upper = mk<ITE> (mk<EQ>(updLower, updUpper), updUpper, upper);
        }

        candidate = mk<DIV>(mk<PLUS>(lower, upper), mkTerm (mpz_class (2), efac));
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
     * Return "e + c"
     */
    Expr getPlusConst(Expr e, bool isInt, int c)
    {
      if (isOpX<MPZ>(e) && isInt)
        return  mkTerm (mpz_class (c + boost::lexical_cast<int> (e)), efac);
      
      Expr ce = isInt ? mkTerm (mpz_class (c), efac) : mkTerm (mpq_class (c), efac);
      return mk<PLUS>(e, ce);
    }
    
    /**
     * Extract function from relation
     */
    Expr getAssignmentForVar(Expr var, Expr exp)
    {
      if (debug) outs () << "getAssignmentForVar " << *var << " in " << *exp << "\n";
      
      bool isInt = bind::isIntConst(var);
      
      if (isOp<ComparissonOp>(exp))
      {

        if (!bind::isBoolConst(var) && var != exp->left())
          exp = ineqReverter(ineqMover(exp, var));
        // TODO: write a similar simplifier fo booleans

        assert (var == exp->left());

        if (isOpX<EQ>(exp) || isOpX<GEQ>(exp) || isOpX<LEQ>(exp)){
          if (exp->left() == exp->right()) return getDefaultAssignment(var);
          return exp->right();
        }
        else if (isOpX<LT>(exp)){
          return getPlusConst (exp->right(), isInt, -1);
        }
        else if (isOpX<GT>(exp)){
          return getPlusConst (exp->right(), isInt, 1);
        }
        else if (isOpX<NEQ>(exp)){
          return getPlusConst (exp->right(), isInt, 1);
        }
        else assert(0);
      }
      else if (isOpX<NEG>(exp)){
        if (isOpX<EQ>(exp->left())) {
          return getPlusConst (getAssignmentForVar(var, exp->left()), isInt, 1);
        }
      }
      else if (isOpX<AND>(exp)){

        exp = u.numericUnderapprox(exp); // try to see if there are only numerals

        if (isOpX<EQ>(exp)) return exp->right();

        bool incomplete = false;

        // split constraints

        ExprSet conjLT;
        ExprSet conjGT;
        ExprSet conjNEG;
        ExprSet conjEG;
        for (auto it = exp->args_begin(), end = exp->args_end(); it != end; ++it){
          Expr cnj = *it;

          // GF: little hack; TODO: make a proper rewriter
          if (isOpX<NEG>(cnj) && isOpX<EQ>(cnj->left())) {
            cnj = mk<NEQ>(cnj->left()->left(), cnj->left()->right());
          }

          cnj = ineqReverter(ineqMover(cnj, var));

          if (isOpX<EQ>(cnj)){
            if (var == cnj->left()) {
              conjEG.insert(cnj->right());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<LT>(cnj) || isOpX<LEQ>(cnj)){
            if (var == cnj->left()) {
              conjLT.insert(cnj->right());
            } else if (var == cnj->right()) {
              conjGT.insert(cnj->left());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<GT>(cnj) || isOpX<GEQ>(cnj)){
            if (var == cnj->left()) {
              conjGT.insert(cnj->right());
            } else if (var == cnj->right()) {
              conjLT.insert(cnj->left());
            } else {
              incomplete = true;
            }
          } else if (isOpX<NEQ>(cnj)){
            if (var == cnj->left()) {
              conjNEG.insert(cnj->right());
            } else {
              incomplete = true;
            }
          }
        }

        // get the assignment (if exists)

        if (conjEG.size() > 0) return *(conjEG.begin()); // GF: maybe try to find the best of them

        if (incomplete && debug) outs() << "WARNING: Some Skolem constraints unsupported\n";

        // get symbolic max and min

        Expr extraDefsMax = mk<TRUE>(efac);
        Expr curMax;
        if (conjGT.size() > 1){
          GetSymbolicMax(conjGT, curMax, isInt);
        } else if (conjGT.size() == 1){
          curMax = *(conjGT.begin());
        }

        Expr extraDefsMin = mk<TRUE>(efac);
        Expr curMin;
        if (conjLT.size() > 1){
          GetSymbolicMin(conjLT, curMin, isInt);
        } else if (conjLT.size() == 1){
          curMin = *(conjLT.begin());
        }

        // get value in the middle of max and min

        if (conjNEG.size() == 0){
          if (conjLT.size() > 0 && conjGT.size() > 0){
            return mk<DIV>(mk<PLUS>(curMin, curMax), mkTerm (mpz_class (2), efac));
          } else {
            if (conjLT.size() == 0){
              return getPlusConst (curMax, isInt, 1);
            } else {
              return getPlusConst (curMin, isInt, -1);
            }
          }
        }

        // here conjNEG.size() > 0

        if (conjLT.size() > 0 && conjGT.size() == 0) {
          conjNEG.insert(curMin);
          GetSymbolicMin(conjNEG, curMin, isInt);
          return getPlusConst (curMin, isInt, -1);
        }

        if (conjLT.size() == 0 && conjGT.size() > 0) {
          conjNEG.insert(curMax);
          GetSymbolicMax(conjNEG, curMax, isInt);
          return getPlusConst (curMax, isInt, 1);
        }

        // now, both conjLT and conjGT are non-empty
        Expr curMid;
        GetSymbolicNeg(conjNEG, curMax, curMin, curMid, isInt);
        return curMid;
      }
      return exp;
    }
    
    /**
     * Check if there are bounded cycles (at most lvl steps) in the map
     */
    bool findCycles(ExprMap &m, Expr var, Expr var2, int lvl=3)
    {
      Expr entr = m[var];
      if (entr == NULL) return false;
      
      ExprSet all;
      filter (entr, bind::IsConst (), inserter (all, all.begin()));
      
      if (!emptyIntersect(var2, all)) return true;
      
      bool res = false;
      if (lvl > 0) for (auto& exp: all) res |= findCycles(m, exp, var2, lvl-1);
      
      return res;
    }
    
    /**
     * Unfolding/simplifying of the map with definitions / substitutions
     */
    void refreshMapEntry (ExprMap &m, Expr var)
    {
      if (debug && false) outs() << "refreshMapEntry for " << *var << "\n";
      
      Expr entr = m[var];
      if (std::find(std::begin(conflictVars), std::end (conflictVars), var) != std::end(conflictVars))
      {
        entr = defMap[var];
        conflictVars.erase(var);
      }
      
      if (entr == NULL) return;
      
      if (conflictVars.empty() && findCycles(m, var, var, 1))
      {
        // FIXME: it does not find all cycles unfortunately
        if (debug) outs () << "cycle found for " << *var << "\n";
        conflictVars.insert(var);
      }
      
      ExprSet skv;
      filter (entr, bind::IsConst (), inserter (skv, skv.begin()));
      
      for (auto& exp2: skv) {
        refreshMapEntry(m, exp2);
        entr = simplifyBool (u.simplifyITE (replaceAll(entr, exp2, m[exp2])));
      }
      
      m[var] = u.numericUnderapprox(mk<EQ>(var, entr))->right();
    }
    
    /**
     * Actually, just print it to cmd in the smt-lib2 format
     */
    void serialize_formula(Expr form)
    {
      smt.reset();
      smt.assertExpr(form);
      
      string errorInfo;
      
      if (errorInfo.empty ())
      {
        smt.toSmtLib (outs());
        outs().flush ();
      }
    }
  };
  
  /**
   * Simple wrapper
   */
  inline void aeSolveAndSkolemize(Expr s, Expr t)
  {
    ExprSet s_vars;
    ExprSet t_vars;
    
    filter (s, bind::IsConst (), inserter (s_vars, s_vars.begin()));
    filter (t, bind::IsConst (), inserter (t_vars, t_vars.begin()));
    
    ExprSet t_quantified = minusSets(t_vars, s_vars);
    
    outs() << "S: " << *s << "\n";
    outs() << "T: \\exists ";
    for (auto &a: t_quantified) outs() << *a << ", ";
    outs() << *t << "\n";
    
    AeValSolver ae(s, t, t_quantified);
    
    Expr res;
    if (ae.solve()){
      res = ae.getValidSubset();
      outs() << "\nvalid subset:\n";
    } else {
      res = ae.getSimpleSkolemFunction();
      outs() << "\nextracted skolem:\n";
    }
    
    ae.serialize_formula(res);
  };
}

#endif
