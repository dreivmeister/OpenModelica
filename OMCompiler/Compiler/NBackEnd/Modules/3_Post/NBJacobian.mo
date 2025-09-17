/*
* This file is part of OpenModelica.
*
* Copyright (c) 1998-2020, Open Source Modelica Consortium (OSMC),
* c/o Linköpings universitet, Department of Computer and Information Science,
* SE-58183 Linköping, Sweden.
*
* All rights reserved.
*
* THIS PROGRAM IS PROVIDED UNDER THE TERMS OF GPL VERSION 3 LICENSE OR
* THIS OSMC PUBLIC LICENSE (OSMC-PL) VERSION 1.2.
* ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES
* RECIPIENT'S ACCEPTANCE OF THE OSMC PUBLIC LICENSE OR THE GPL VERSION 3,
* ACCORDING TO RECIPIENTS CHOICE.
*
* The OpenModelica software and the Open Source Modelica
* Consortium (OSMC) Public License (OSMC-PL) are obtained
* from OSMC, either from the above address,
* from the URLs: http://www.ida.liu.se/projects/OpenModelica or
* http://www.openmodelica.org, and in the OpenModelica distribution.
* GNU version 3 is obtained from: http://www.gnu.org/copyleft/gpl.html.
*
* This program is distributed WITHOUT ANY WARRANTY; without
* even the implied warranty of  MERCHANTABILITY or FITNESS
* FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
* IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS OF OSMC-PL.
*
* See the full OSMC Public License conditions for more details.
*
*/
encapsulated package NBJacobian
"file:        NBJacobian.mo
 package:     NBJacobian
 description: This file contains the functions to create and manipulate jacobians.
              The main type is inherited from NBackendDAE.mo
              NOTE: There is no real jacobian type, it is a BackendDAE.
"

public
  import BackendDAE = NBackendDAE;
  import Module = NBModule;

protected
  // NF imports
  import ComponentRef = NFComponentRef;
  import Expression = NFExpression;
  import NFFlatten.FunctionTree;
  import Operator = NFOperator;
  import SimplifyExp = NFSimplifyExp;
  import Type = NFType;
  import Variable = NFVariable;

  // Backend imports
  import Adjacency = NBAdjacency;
  import NBAdjacency.Mapping;
  import BEquation = NBEquation;
  import BVariable = NBVariable;
  import Differentiate = NBDifferentiate;
  import NBDifferentiate.{DifferentiationArguments, DifferentiationType};
  import NBEquation.{Equation, EquationPointers, EquationPointer, EqData};
  import Jacobian = NBackendDAE.BackendDAE;
  import Matching = NBMatching;
  import Replacements = NBReplacements;
  import Sorting = NBSorting;
  import StrongComponent = NBStrongComponent;
  import Partition = NBPartition;
  import NFOperator.{MathClassification, SizeClassification};
  import NBVariable.{VariablePointers, VariablePointer, VarData};

  // Old Backend Import (remove once coloring ins ported)
  import SymbolicJacobian;

  // Util imports
  import AvlSetPath;
  import StringUtil;
  import UnorderedMap;
  import UnorderedSet;
  import Util;

public
  type JacobianType = enumeration(ODE, DAE, LS, NLS);

  function isDynamic
    "is the jacobian used for integration (-> ture)
     or solving algebraic systems (-> false)?"
    input JacobianType jacType;
    output Boolean b;
  algorithm
    b := match jacType
      case JacobianType.ODE then true;
      case JacobianType.DAE then true;
      else false;
    end match;
  end isDynamic;

  function main
    "Wrapper function for any jacobian function. This will be called during
     simulation and gets the corresponding subfunction from Config."
    extends Module.wrapper;
    input Partition.Kind kind;
  protected
    constant Module.jacobianInterface func = getModule();
  algorithm
    bdae := match bdae
      local
        String name                                     "Context name for jacobian";
        VariablePointers knowns                         "Variable array of knowns";
        FunctionTree funcTree                           "Function call bodies";
        list<Partition.Partition> oldPartitions, newPartitions = {} "Equation partitions before and afterwards";
        list<Partition.Partition> oldEvents, newEvents = {}   "Event Equation partitions before and afterwards";

      case BackendDAE.MAIN(varData = BVariable.VAR_DATA_SIM(knowns = knowns), funcTree = funcTree)
        algorithm
          (oldPartitions, name) := match kind
            case NBPartition.Kind.ODE then (bdae.ode, "ODE_JAC");
            case NBPartition.Kind.DAE then (Util.getOption(bdae.dae), "DAE_JAC");
            else algorithm
              Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed for: " + Partition.Partition.kindToString(kind)});
            then fail();
          end match;
          oldEvents := bdae.ode_event;

          if Flags.isSet(Flags.JAC_DUMP) then
            print(StringUtil.headline_1("[symjacdump] Creating symbolic Jacobians:") + "\n");
          end if;

          for part in listReverse(oldPartitions) loop
            (part, funcTree) := partJacobian(part, funcTree, knowns, name, func);
            newPartitions := part::newPartitions;
          end for;

          for part in listReverse(oldEvents) loop
            (part, funcTree) := partJacobian(part, funcTree, knowns, name, func);
            newEvents := part::newEvents;
          end for;

          () := match kind
            case NBPartition.Kind.ODE algorithm bdae.ode := newPartitions; then ();
            case NBPartition.Kind.DAE algorithm bdae.dae := SOME(newPartitions); then ();
            else ();
          end match;
          bdae.ode_event := newEvents;
          bdae.funcTree := funcTree;
      then bdae;

      else algorithm
        // maybe add failtrace here and allow failing
        Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed for: " + BackendDAE.toString(bdae)});
      then fail();

    end match;
  end main;

  function nonlinear
    input VariablePointers variables;
    input EquationPointers equations;
    input array<StrongComponent> comps;
    output Option<Jacobian> jacobian;
    input output FunctionTree funcTree;
    input String name;
    input Boolean init;
  protected
    constant Module.jacobianInterface func = if Flags.isSet(Flags.NLS_ANALYTIC_JACOBIAN)
      then jacobianSymbolic
      else jacobianNumeric;
  algorithm
    (jacobian, funcTree) := func(
        name              = name,
        jacType           = JacobianType.NLS,
        seedCandidates    = variables,
        partialCandidates = EquationPointers.getResiduals(equations),      // these have to be updated once there are inner equations in torn partitions
        equations         = equations,
        knowns            = VariablePointers.empty(0),      // remove them? are they necessary?
        strongComponents  = SOME(comps),
        funcTree          = funcTree,
        init              = init
      );
  end nonlinear;

  function combine
    input list<BackendDAE> jacobians;
    input String name;
    output BackendDAE jacobian;
  protected
    JacobianType jacType;
    list<Pointer<Variable>> variables = {}, unknowns = {}, knowns = {}, auxiliaryVars = {}, aliasVars = {};
    list<Pointer<Variable>> diffVars = {}, dependencies = {}, resultVars = {}, tmpVars = {}, seedVars = {};
    list<StrongComponent> comps = {};
    list<SparsityPatternCol> col_wise_pattern = {};
    list<SparsityPatternRow> row_wise_pattern = {};
    list<ComponentRef> seed_vars = {};
    list<ComponentRef> partial_vars = {};
    Integer nnz = 0;
    VarData varData;
    EqData eqData;
    SparsityPattern sparsityPattern;
    SparsityColoring sparsityColoring = SparsityColoring.lazy(EMPTY_SPARSITY_PATTERN);
  algorithm

    if List.hasOneElement(jacobians) then
      jacobian := listHead(jacobians);
      jacobian := match jacobian case BackendDAE.JACOBIAN() algorithm jacobian.name := name; then jacobian; end match;
    else
      for jac in jacobians loop
        () := match jac
          local
            VarData tmpVarData;
            SparsityPattern tmpPattern;

          case BackendDAE.JACOBIAN(varData = tmpVarData as VarData.VAR_DATA_JAC(), sparsityPattern = tmpPattern) algorithm
            jacType       := jac.jacType;
            variables     := listAppend(VariablePointers.toList(tmpVarData.variables), variables);
            unknowns      := listAppend(VariablePointers.toList(tmpVarData.unknowns), unknowns);
            knowns        := listAppend(VariablePointers.toList(tmpVarData.knowns), knowns);
            auxiliaryVars := listAppend(VariablePointers.toList(tmpVarData.auxiliaries), auxiliaryVars);
            aliasVars     := listAppend(VariablePointers.toList(tmpVarData.aliasVars), aliasVars);
            diffVars      := listAppend(VariablePointers.toList(tmpVarData.diffVars), diffVars);
            dependencies  := listAppend(VariablePointers.toList(tmpVarData.dependencies), dependencies);
            resultVars    := listAppend(VariablePointers.toList(tmpVarData.resultVars), resultVars);
            tmpVars       := listAppend(VariablePointers.toList(tmpVarData.tmpVars), tmpVars);
            seedVars      := listAppend(VariablePointers.toList(tmpVarData.seedVars), seedVars);

            comps         := listAppend(arrayList(jac.comps), comps);

            col_wise_pattern  := listAppend(tmpPattern.col_wise_pattern, col_wise_pattern);
            row_wise_pattern  := listAppend(tmpPattern.row_wise_pattern, row_wise_pattern);
            seed_vars         := listAppend(tmpPattern.seed_vars, seed_vars);
            partial_vars      := listAppend(tmpPattern.partial_vars, partial_vars);
            nnz               := nnz + tmpPattern.nnz;
            sparsityColoring  := SparsityColoring.combine(sparsityColoring, jac.sparsityColoring);
          then ();

          else algorithm
            Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed for\n" + BackendDAE.toString(jac)});
          then fail();
        end match;
      end for;

      varData := VarData.VAR_DATA_JAC(
        variables     = VariablePointers.fromList(variables),
        unknowns      = VariablePointers.fromList(unknowns),
        knowns        = VariablePointers.fromList(knowns),
        auxiliaries   = VariablePointers.fromList(auxiliaryVars),
        aliasVars     = VariablePointers.fromList(aliasVars),
        diffVars      = VariablePointers.fromList(diffVars),
        dependencies  = VariablePointers.fromList(dependencies),
        resultVars    = VariablePointers.fromList(resultVars),
        tmpVars       = VariablePointers.fromList(tmpVars),
        seedVars      = VariablePointers.fromList(seedVars)
      );

      sparsityPattern := SPARSITY_PATTERN(
        col_wise_pattern  = col_wise_pattern,
        row_wise_pattern  = row_wise_pattern,
        seed_vars         = seed_vars,
        partial_vars      = partial_vars,
        nnz               = nnz
      );

      jacobian := BackendDAE.JACOBIAN(
        name              = name,
        jacType           = jacType,
        varData           = varData,
        comps             = listArray(comps),
        sparsityPattern   = sparsityPattern,
        sparsityColoring  = sparsityColoring
      );
    end if;
  end combine;

  function getModule
    "Returns the module function that was chosen by the user."
    output Module.jacobianInterface func;
  algorithm
    func := match Flags.getConfigString(Flags.GENERATE_DYNAMIC_JACOBIAN)
      case "symbolic" then jacobianSymbolic;
      case "adjoint" then jacobianSymbolic;
      case "parameter" then jacobianSymbolicParameters;
      case "parameteradjoint" then jacobianSymbolicParameters;
      case "numeric"  then jacobianNumeric;
      case "none"     then jacobianNone;
    end match;
  end getModule;

  function toString
    input BackendDAE jacobian;
    input output String str;
  algorithm
    str := BackendDAE.toString(jacobian, str);
  end toString;

  function jacobianTypeString
    input JacobianType jacType;
    output String str;
  algorithm
    str := match jacType
      case JacobianType.ODE then "[ODE]";
      case JacobianType.DAE then "[DAE]";
      case JacobianType.LS  then "[LS-]";
      case JacobianType.NLS then "[NLS]";
                            else "[ERR]";
    end match;
  end jacobianTypeString;

  // necessary as wrapping value type for UnorderedMap
  type CrefLst = list<ComponentRef>;

  type SparsityPatternCol = tuple<ComponentRef, list<ComponentRef>> "partial_vars, {seed_vars}";
  type SparsityPatternRow = SparsityPatternCol                      "seed_vars, {partial_vars}";

  uniontype SparsityPattern
    record SPARSITY_PATTERN
      list<SparsityPatternCol> col_wise_pattern   "colum-wise sparsity pattern";
      list<SparsityPatternRow> row_wise_pattern   "row-wise sparsity pattern";
      list<ComponentRef> seed_vars                "independent variables solved here ($SEED)";
      list<ComponentRef> partial_vars             "LHS variables of the jacobian ($pDER)";
      Integer nnz                                 "number of nonzero elements";
    end SPARSITY_PATTERN;

    function toString
      input SparsityPattern pattern;
      output String str = StringUtil.headline_2("Sparsity Pattern (nnz: " + intString(pattern.nnz) + ")");
    protected
      ComponentRef cref;
      list<ComponentRef> dependencies;
      Boolean colEmpty = listEmpty(pattern.col_wise_pattern);
      Boolean rowEmpty = listEmpty(pattern.row_wise_pattern);
    algorithm
      str := str + "\n" + StringUtil.headline_3("### Seeds (col vars) ###");
      str := str + List.toString(pattern.seed_vars, ComponentRef.toString) + "\n";
      str := str + "\n" + StringUtil.headline_3("### Partials (row vars) ###");
      str := str + List.toString(pattern.partial_vars, ComponentRef.toString) + "\n";
      if not colEmpty then
        str := str + "\n" + StringUtil.headline_3("### Columns ###");
        for col in pattern.col_wise_pattern loop
          (cref, dependencies) := col;
          str := str + "(" + ComponentRef.toString(cref) + ")\t affects:\t" + ComponentRef.listToString(dependencies) + "\n";
        end for;
      end if;
      if not rowEmpty then
        str := str + "\n" + StringUtil.headline_3("##### Rows #####");
        for row in pattern.row_wise_pattern loop
          (cref, dependencies) := row;
          str := str + "(" + ComponentRef.toString(cref) + ")\t depends on:\t" + ComponentRef.listToString(dependencies) + "\n";
        end for;
      end if;
    end toString;

    function lazy
      input VariablePointers seedCandidates;
      input VariablePointers partialCandidates;
      input Option<array<StrongComponent>> strongComponents "Strong Components";
      input JacobianType jacType;
      output SparsityPattern sparsityPattern;
      output SparsityColoring sparsityColoring;
    protected
      list<ComponentRef> seed_vars, partial_vars;
      list<SparsityPatternCol> cols = {};
      list<SparsityPatternRow> rows = {};
      Integer nnz;
    algorithm
      // get all relevant crefs
      seed_vars     := VariablePointers.getScalarVarNames(seedCandidates);
      partial_vars  := VariablePointers.getScalarVarNames(partialCandidates);

      // assume full dependency
      cols := list((s, partial_vars) for s in seed_vars);
      rows := list((p, seed_vars) for p in partial_vars);
      nnz := listLength(partial_vars) * listLength(seed_vars);

      sparsityPattern := SPARSITY_PATTERN(cols, rows, seed_vars, partial_vars, nnz);
      sparsityColoring := SparsityColoring.lazy(sparsityPattern);
    end lazy;

    function create
      input VariablePointers seedCandidates;
      input VariablePointers partialCandidates;
      input Option<array<StrongComponent>> strongComponents "Strong Components";
      input JacobianType jacType;
      output SparsityPattern sparsityPattern;
      output SparsityColoring sparsityColoring;
    protected
      UnorderedMap<ComponentRef, list<ComponentRef>> map;
    algorithm
      (sparsityPattern, map) := match strongComponents
        local
          Mapping seed_mapping, partial_mapping;
          array<StrongComponent> comps;
          list<ComponentRef> seed_vars, seed_vars_array, partial_vars, partial_vars_array, tmp, row_vars = {}, col_vars = {};
          UnorderedSet<ComponentRef> set;
          list<SparsityPatternCol> cols = {};
          list<SparsityPatternRow> rows = {};
          Integer nnz = 0;

        case SOME(comps) guard(arrayEmpty(comps)) algorithm
        then (EMPTY_SPARSITY_PATTERN, UnorderedMap.new<CrefLst>(ComponentRef.hash, ComponentRef.isEqual));

        case SOME(comps) algorithm
          // create index mapping only for variables
          seed_mapping    := Mapping.create(EquationPointers.empty(), seedCandidates);
          partial_mapping := Mapping.create(EquationPointers.empty(), partialCandidates);

          // get all relevant crefs
          partial_vars        := VariablePointers.getScalarVarNames(partialCandidates);
          seed_vars           := VariablePointers.getScalarVarNames(seedCandidates);
          // unscalarized seed vars are currently needed for sparsity pattern
          seed_vars_array     := VariablePointers.getVarNames(seedCandidates);
          partial_vars_array  := VariablePointers.getVarNames(partialCandidates);

          // create a sufficient big unordered map
          map := UnorderedMap.new<CrefLst>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(seed_vars) + listLength(partial_vars)));
          set := UnorderedSet.new(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(seed_vars_array)));

          // save all seed_vars and partial_vars to know later on if a cref should be added
          for cref in seed_vars loop UnorderedMap.add(cref, {}, map); end for;
          for cref in partial_vars loop UnorderedMap.add(cref, {}, map); end for;
          for cref in seed_vars_array loop UnorderedSet.add(cref, set); end for;
          for cref in partial_vars_array loop UnorderedSet.add(cref, set); end for;

          // traverse all components and save cref dependencies (only column-wise)
          for i in 1:arrayLength(comps) loop
            StrongComponent.collectCrefs(comps[i], seedCandidates, partialCandidates, seed_mapping, partial_mapping, map, set, jacType);
          end for;

          // create row-wise sparsity pattern
          for cref in listReverse(partial_vars) loop
            // only create rows for derivatives
            if jacType == JacobianType.NLS or BVariable.checkCref(cref, BVariable.isStateDerivative, sourceInfo()) or BVariable.checkCref(cref, BVariable.isResidual, sourceInfo()) then
              if UnorderedMap.contains(cref, map) then
                tmp := UnorderedSet.unique_list(UnorderedMap.getOrFail(cref, map), ComponentRef.hash, ComponentRef.isEqual);
                rows := (cref, tmp) :: rows;
                row_vars := cref :: row_vars;
                for dep in tmp loop
                  // also add inverse dependency (indep var) --> (res/tmp) :: rest
                  UnorderedMap.add(dep, cref :: UnorderedMap.getSafe(dep, map, sourceInfo()), map);
                end for;
              end if;
            end if;
          end for;

          // create column-wise sparsity pattern
          for cref in listReverse(seed_vars) loop
            if jacType == JacobianType.NLS or BVariable.checkCref(cref, BVariable.isState, sourceInfo()) then
              tmp := UnorderedSet.unique_list(UnorderedMap.getSafe(cref, map, sourceInfo()), ComponentRef.hash, ComponentRef.isEqual);
              cols := (cref, tmp) :: cols;
              col_vars := cref :: col_vars;
            end if;
          end for;

          // find number of nonzero elements
          for col in cols loop
            (_, tmp) := col;
            nnz := nnz + listLength(tmp);
          end for;
        then (SPARSITY_PATTERN(cols, rows, listReverse(col_vars), listReverse(row_vars), nnz), map);

        case NONE() algorithm
          Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because of missing strong components."});
        then fail();

        else algorithm
          Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed."});
        then fail();

      end match;

      // create coloring
      sparsityColoring := SparsityColoring.PartialD2ColoringAlgC(sparsityPattern, jacType);

      if Flags.isSet(Flags.DUMP_SPARSE) then
        print(toString(sparsityPattern) + "\n" + SparsityColoring.toString(sparsityColoring) + "\n");
      end if;
    end create;

    function createEmpty
      output SparsityPattern sparsityPattern = EMPTY_SPARSITY_PATTERN;
      output SparsityColoring sparsityColoring = EMPTY_SPARSITY_COLORING;
    end createEmpty;

    // function transposeRenamed
    //   "Transpose a sparsity pattern while applying renaming maps:
    //      oldPartial -> newSeed
    //      oldSeed    -> newPartial
    //    Inputs:
    //      pattern: original forward sparsity
    //      mapPartialToNewSeed:  old partial_vars cref  -> new seed cref
    //      mapSeedToNewPDer:     old seed_vars cref     -> new partial (pDer) cref
    //    Output:
    //      transposedPattern: with
    //        seed_vars    = (renamed old partials)
    //        partial_vars = (renamed old seeds)
    //        col_wise_pattern: each new seed (old partial) -> list of new partials (old seeds)
    //        row_wise_pattern: inverse."
    //   input SparsityPattern pattern;
    //   input UnorderedMap<ComponentRef, ComponentRef> mapPartialToNewSeed;
    //   input UnorderedMap<ComponentRef, ComponentRef> mapSeedToNewPDer;
    //   input JacobianType jacType;
    //   output SparsityPattern transposedPattern;
    //   output SparsityColoring transposedColoring;
    // protected
    //   list<SparsityPatternCol> newCols = {};
    //   list<SparsityPatternRow> newRows = {};
    //   list<ComponentRef> newSeedVars = {};
    //   list<ComponentRef> newPartialVars = {};
    //   ComponentRef oldCref, newCref;
    //   list<ComponentRef> oldDeps, newDeps;
    //   Integer nnz = 0;
    //   ComponentRef depOld, depNew;


    //   UnorderedMap<ComponentRef, list<ComponentRef>> inv =
    //     UnorderedMap.new<CrefLst>(ComponentRef.hash, ComponentRef.isEqual);
    //   ComponentRef seedNew, partNew;
    //   list<ComponentRef> partsLst;
    // algorithm
    //   // Build new seed vars (renamed old partials)
    //   for oldCref in pattern.partial_vars loop
    //     if UnorderedMap.contains(oldCref, mapPartialToNewSeed) then
    //       newCref := UnorderedMap.getOrFail(oldCref, mapPartialToNewSeed);
    //       newSeedVars := newCref :: newSeedVars;
    //     else
    //       // skip if no rename (should not happen)
    //     end if;
    //   end for;
    //   newSeedVars := listReverse(newSeedVars);

    //   // Build new partial vars (renamed old seeds)
    //   for oldCref in pattern.seed_vars loop
    //     if UnorderedMap.contains(oldCref, mapSeedToNewPDer) then
    //       newCref := UnorderedMap.getOrFail(oldCref, mapSeedToNewPDer);
    //       newPartialVars := newCref :: newPartialVars;
    //     end if;
    //   end for;
    //   newPartialVars := listReverse(newPartialVars);

    //   // Column-wise (use old row_wise_pattern: (oldPartial -> list oldSeeds))
    //   for tpl in pattern.row_wise_pattern loop
    //     (oldCref, oldDeps) := tpl;
    //     if UnorderedMap.contains(oldCref, mapPartialToNewSeed) then
    //       newCref := UnorderedMap.getOrFail(oldCref, mapPartialToNewSeed);
    //       newDeps := {};
    //       for depOld in oldDeps loop
    //         if UnorderedMap.contains(depOld, mapSeedToNewPDer) then
    //           depNew := UnorderedMap.getOrFail(depOld, mapSeedToNewPDer);
    //           newDeps := depNew :: newDeps;
    //         end if;
    //       end for;
    //       newDeps := listReverse(newDeps);
    //       newCols := (newCref, newDeps) :: newCols;
    //       nnz := nnz + listLength(newDeps);
    //     end if;
    //   end for;
    //   newCols := listReverse(newCols);

    //   // Row-wise (inverse of newCols)
    //   // Build inverse map: for each (seed -> partials) add seed to each partial's dependency list
    //   // Use temporary map
    //   for col in newCols loop
    //     (seedNew, partsLst) := col;
    //     for partNew in partsLst loop
    //       UnorderedMap.add(partNew, seedNew :: UnorderedMap.getSafe(partNew, inv, sourceInfo()), inv);
    //     end for;
    //   end for;

    //   for partNew in newPartialVars loop
    //     newDeps := UnorderedSet.unique_list(UnorderedMap.getSafe(partNew, inv, sourceInfo()), ComponentRef.hash, ComponentRef.isEqual);
    //     newRows := (partNew, newDeps) :: newRows;
    //   end for;
    //   newRows := listReverse(newRows);

    //   transposedPattern := SPARSITY_PATTERN(
    //     col_wise_pattern = newCols,
    //     row_wise_pattern = newRows,
    //     seed_vars        = newSeedVars,
    //     partial_vars     = newPartialVars,
    //     nnz              = nnz
    //   );

    //   // Re-color
    //   transposedColoring := SparsityColoring.PartialD2ColoringAlgC(transposedPattern, jacType);
    // end transposeRenamed;

    function transposeRenamed
      "Transpose a sparsity pattern while applying renaming maps:
         oldPartial -> newSeed
         oldSeed    -> newPartial (pDer)
       The new col_wise is the renamed old row_wise,
       and the new row_wise is the renamed old col_wise."
      input SparsityPattern pattern;
      input UnorderedMap<ComponentRef, ComponentRef> mapPartialToNewSeed;
      input UnorderedMap<ComponentRef, ComponentRef> mapSeedToNewPDer;
      input JacobianType jacType;
      output SparsityPattern transposedPattern;
      output SparsityColoring transposedColoring;
    protected
      list<SparsityPatternCol> newCols = {};
      list<SparsityPatternRow> newRows = {};
      list<ComponentRef> newSeedVars = {};
      list<ComponentRef> newPartialVars = {};
      ComponentRef oldHead, newHead, depOld, depNew;
      list<ComponentRef> deps, newDeps;
      Integer nnz = 0;
    algorithm
      // New seed_vars = renamed old partials
      for oldHead in pattern.partial_vars loop
        if UnorderedMap.contains(oldHead, mapPartialToNewSeed) then
          newSeedVars := UnorderedMap.getOrFail(oldHead, mapPartialToNewSeed) :: newSeedVars;
        end if;
      end for;
      newSeedVars := listReverse(newSeedVars);

      // New partial_vars = renamed old seeds
      for oldHead in pattern.seed_vars loop
        if UnorderedMap.contains(oldHead, mapSeedToNewPDer) then
          newPartialVars := UnorderedMap.getOrFail(oldHead, mapSeedToNewPDer) :: newPartialVars;
        end if;
      end for;
      newPartialVars := listReverse(newPartialVars);

      // New columns = renamed old rows (oldPartial -> list oldSeeds)
      for row in pattern.row_wise_pattern loop
        (oldHead, deps) := row;
        if UnorderedMap.contains(oldHead, mapPartialToNewSeed) then
          newHead := UnorderedMap.getOrFail(oldHead, mapPartialToNewSeed);
          newDeps := {};
          for depOld in deps loop
            if UnorderedMap.contains(depOld, mapSeedToNewPDer) then
              depNew := UnorderedMap.getOrFail(depOld, mapSeedToNewPDer);
              newDeps := depNew :: newDeps;
            end if;
          end for;
          // keep unique deps and stable order
          newDeps := UnorderedSet.unique_list(listReverse(newDeps), ComponentRef.hash, ComponentRef.isEqual);
          newCols := (newHead, newDeps) :: newCols;
          nnz := nnz + listLength(newDeps);
        end if;
      end for;
      newCols := listReverse(newCols);

      // New rows = renamed old columns (oldSeed -> list oldPartials)
      for col in pattern.col_wise_pattern loop
        (oldHead, deps) := col;
        if UnorderedMap.contains(oldHead, mapSeedToNewPDer) then
          newHead := UnorderedMap.getOrFail(oldHead, mapSeedToNewPDer);
          newDeps := {};
          for depOld in deps loop
            if UnorderedMap.contains(depOld, mapPartialToNewSeed) then
              depNew := UnorderedMap.getOrFail(depOld, mapPartialToNewSeed);
              newDeps := depNew :: newDeps;
            end if;
          end for;
          newDeps := UnorderedSet.unique_list(listReverse(newDeps), ComponentRef.hash, ComponentRef.isEqual);
          newRows := (newHead, newDeps) :: newRows;
        end if;
      end for;
      newRows := listReverse(newRows);

      transposedPattern := SPARSITY_PATTERN(
        col_wise_pattern = newCols,
        row_wise_pattern = newRows,
        seed_vars        = newSeedVars,
        partial_vars     = newPartialVars,
        nnz              = nnz
      );

      print("Transposed Sparsity Pattern:\n" + toString(transposedPattern) + "\n");

      // Re-color after transpose
      transposedColoring := SparsityColoring.PartialD2ColoringAlgC(transposedPattern, jacType);
    end transposeRenamed;
  end SparsityPattern;

  constant SparsityPattern EMPTY_SPARSITY_PATTERN = SPARSITY_PATTERN({}, {}, {}, {}, 0);
  constant SparsityColoring EMPTY_SPARSITY_COLORING = SPARSITY_COLORING(listArray({}), listArray({}));

  type SparsityColoringCol = list<ComponentRef>  "seed variable lists belonging to the same color";
  type SparsityColoringRow = SparsityColoringCol "partial variable lists for each color (multiples allowed!)";

  uniontype SparsityColoring
    record SPARSITY_COLORING
      "column wise coloring with extra row sparsity information"
      array<SparsityColoringCol> cols;
      array<SparsityColoringRow> rows;
    end SPARSITY_COLORING;

    function toString
      input SparsityColoring sparsityColoring;
      output String str = StringUtil.headline_2("Sparsity Coloring");
    protected
      Boolean empty = arrayLength(sparsityColoring.cols) == 0;
    algorithm
      if empty then
        str := str + "\n<empty sparsity pattern>\n";
      end if;
      for i in 1:arrayLength(sparsityColoring.cols) loop
        str := str + "Color (" + intString(i) + ")\n"
          + "  - Column: " + ComponentRef.listToString(sparsityColoring.cols[i]) + "\n"
          + "  - Row:    " + ComponentRef.listToString(sparsityColoring.rows[i]) + "\n\n";
      end for;
    end toString;

    function lazy
      "creates a lazy coloring that just groups each independent variable individually
      and implies dependence for each row"
      input SparsityPattern sparsityPattern;
      output SparsityColoring sparsityColoring;
    protected
      array<SparsityColoringCol> cols;
      array<SparsityColoringRow> rows;
    algorithm
      cols := listArray(list({cref} for cref in sparsityPattern.seed_vars));
      rows := arrayCreate(arrayLength(cols), sparsityPattern.partial_vars);
      sparsityColoring := SPARSITY_COLORING(cols, rows);
    end lazy;

    function PartialD2ColoringAlgC
      "author: kabdelhak 2022-03
      taken from: 'What Color Is Your Jacobian? Graph Coloring for Computing Derivatives'
      https://doi.org/10.1137/S0036144504444711
      A greedy partial distance-2 coloring algorithm implemented in C."
      input SparsityPattern sparsityPattern;
      input JacobianType jacType;
      output SparsityColoring sparsityColoring;
    protected
      array<ComponentRef> seeds, partials;
      UnorderedMap<ComponentRef, Integer> seed_indices, partial_indices;
      Integer sizeCols, sizeRows;
      ComponentRef idx_cref;
      list<ComponentRef> deps;
      array<list<Integer>> cols, rows, colored_cols;
      array<SparsityColoringCol> cref_colored_cols;
    algorithm
      // create index -> cref arrays
      seeds := listArray(sparsityPattern.seed_vars);
      if jacType == JacobianType.NLS then
        partials := listArray(sparsityPattern.partial_vars);
      else
        partials := listArray(list(cref for cref guard(BVariable.checkCref(cref, BVariable.isStateDerivative, sourceInfo()) or
          BVariable.checkCref(cref, BVariable.isResidual, sourceInfo())) in sparsityPattern.partial_vars));
      end if;

      // create cref -> index maps
      sizeCols := arrayLength(seeds);
      sizeRows := arrayLength(partials);
      seed_indices := UnorderedMap.new<Integer>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(sizeCols));
      partial_indices := UnorderedMap.new<Integer>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(sizeRows));
      for i in 1:sizeCols loop
        UnorderedMap.add(seeds[i], i, seed_indices);
      end for;
      for i in 1:sizeRows loop
        UnorderedMap.add(partials[i], i, partial_indices);
      end for;
      cols := arrayCreate(sizeCols, {});
      rows := arrayCreate(sizeRows, {});

      // prepare index based sparsity pattern for C
      for tpl in sparsityPattern.col_wise_pattern loop
        (idx_cref, deps) := tpl;
        cols[UnorderedMap.getSafe(idx_cref, seed_indices, sourceInfo())] := list(UnorderedMap.getSafe(dep, partial_indices, sourceInfo()) for dep in deps);
      end for;
      for tpl in sparsityPattern.row_wise_pattern loop
        (idx_cref, deps) := tpl;
        rows[UnorderedMap.getSafe(idx_cref, partial_indices, sourceInfo())] := list(UnorderedMap.getSafe(dep, seed_indices, sourceInfo()) for dep in deps);
      end for;

      // call C function (old backend - ToDo: port to new backend!)
      //colored_cols := SymbolicJacobian.createColoring(cols, rows, sizeRows, sizeCols);
      colored_cols := SymbolicJacobian.createColoring(rows, cols, sizeCols, sizeRows);

      // get cref based coloring - currently no row coloring
      cref_colored_cols := arrayCreate(arrayLength(colored_cols), {});
      for i in 1:arrayLength(colored_cols) loop
        cref_colored_cols[i] := list(seeds[idx] for idx in colored_cols[i]);
      end for;

      sparsityColoring := SPARSITY_COLORING(cref_colored_cols, arrayCreate(sizeRows, {}));
    end PartialD2ColoringAlgC;

    function PartialD2ColoringAlg
      "author: kabdelhak 2022-03
      taken from: 'What Color Is Your Jacobian? Graph Coloring for Computing Derivatives'
      https://doi.org/10.1137/S0036144504444711
      A greedy partial distance-2 coloring algorithm. Slightly adapted to also track row sparsity."
      input SparsityPattern sparsityPattern;
      input UnorderedMap<ComponentRef, list<ComponentRef>> map;
      output SparsityColoring sparsityColoring;
    protected
      array<ComponentRef> cref_lookup;
      UnorderedMap<ComponentRef, Integer> index_lookup;
      array<Boolean> color_exists;
      array<Integer> coloring, forbidden_colors;
      array<list<ComponentRef>> col_coloring, row_coloring;
      Integer color;
      list<SparsityColoringCol> cols_lst = {};
      list<SparsityColoringRow> rows_lst = {};
    algorithm
      // integer to cref and reverse lookup arrays
      cref_lookup := listArray(sparsityPattern.seed_vars);
      index_lookup := UnorderedMap.new<Integer>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(sparsityPattern.seed_vars)));
      for i in 1:arrayLength(cref_lookup) loop
        UnorderedMap.add(cref_lookup[i], i, index_lookup);
      end for;

      // create empty colorings
      coloring := arrayCreate(arrayLength(cref_lookup), 0);
      forbidden_colors := arrayCreate(arrayLength(cref_lookup), 0);
      color_exists := arrayCreate(arrayLength(cref_lookup), false);
      col_coloring := arrayCreate(arrayLength(cref_lookup), {});
      row_coloring := arrayCreate(arrayLength(cref_lookup), {});

      for i in 1:arrayLength(cref_lookup) loop
        for row_var /* w */ in UnorderedMap.getSafe(cref_lookup[i], map, sourceInfo()) loop
          for col_var /* x */ in UnorderedMap.getSafe(row_var, map, sourceInfo()) loop
            color := coloring[UnorderedMap.getSafe(col_var, index_lookup, sourceInfo())];
            if color > 0 then
              forbidden_colors[color] := i;
            end if;
          end for;
        end for;
        color := 1;
        while forbidden_colors[color] == i loop
          color := color + 1;
        end while;
        coloring[i] := color;
        // also save all row dependencies of this color
        row_coloring[color] := listAppend(row_coloring[color], UnorderedMap.getSafe(cref_lookup[i], map, sourceInfo()));
        color_exists[color] := true;
      end for;

      for i in 1:arrayLength(coloring) loop
        col_coloring[coloring[i]] := cref_lookup[i] :: col_coloring[coloring[i]];
      end for;

      // traverse in reverse to have correct ordering in the end)
      for i in arrayLength(color_exists):-1:1 loop
        if color_exists[i] then
          cols_lst := col_coloring[i] :: cols_lst;
          rows_lst := row_coloring[i] :: rows_lst;
        end if;
      end for;

      sparsityColoring := SPARSITY_COLORING(listArray(cols_lst), listArray(rows_lst));
    end PartialD2ColoringAlg;

    function combine
      "combines sparsity patterns by just appending them because they are supposed to
      be entirely independent of each other."
      input SparsityColoring coloring1;
      input SparsityColoring coloring2;
      output SparsityColoring coloring_out;
    protected
      SparsityColoring smaller_coloring;
    algorithm
      // append the smaller to the bigger
      (coloring_out, smaller_coloring) := if arrayLength(coloring2.cols) > arrayLength(coloring1.cols) then (coloring2, coloring1) else (coloring1, coloring2);

      for i in 1:arrayLength(smaller_coloring.cols) loop
        coloring_out.cols[i] := listAppend(coloring_out.cols[i], smaller_coloring.cols[i]);
        coloring_out.rows[i] := listAppend(coloring_out.rows[i], smaller_coloring.rows[i]);
      end for;
    end combine;
  end SparsityColoring;

protected
  // ToDo: all the DAEMode stuff is probably incorrect!

  function partJacobian
    input output Partition.Partition part;
    input output FunctionTree funcTree;
    input VariablePointers knowns;
    input String name                                     "Context name for jacobian";
    input Module.jacobianInterface func;
  protected
    JacobianType jacType;
    VariablePointers unknowns;
    list<Pointer<Variable>> derivative_vars, state_vars, param_vars;
    VariablePointers seedCandidates, partialCandidates;
    Option<Jacobian> jacobian, jacobianAdjoint  "Resulting jacobians";
    Jacobian jacobianUnwrap, jacobianWrap;
    array<StrongComponent> inlined_comps;
    Partition.Kind kind = Partition.Partition.getKind(part);
  algorithm
    partialCandidates := part.unknowns;
    unknowns  := if Partition.Partition.getKind(part) == NBPartition.Kind.DAE then Util.getOption(part.daeUnknowns) else part.unknowns;
    jacType   := if Partition.Partition.getKind(part) == NBPartition.Kind.DAE then JacobianType.DAE else JacobianType.ODE;

    derivative_vars := list(var for var guard(BVariable.isStateDerivative(var)) in VariablePointers.toList(unknowns));

    if Flags.getConfigString(Flags.GENERATE_DYNAMIC_JACOBIAN) == "parameter" or Flags.getConfigString(Flags.GENERATE_DYNAMIC_JACOBIAN) == "parameteradjoint" then
      param_vars := list(var for var guard (BVariable.isParam(var)) in VariablePointers.toList(knowns));
      seedCandidates := VariablePointers.fromList(param_vars, partialCandidates.scalarized);
    else
      state_vars := list(Util.getOption(BVariable.getVarState(var)) for var in derivative_vars);
      seedCandidates := VariablePointers.fromList(state_vars, partialCandidates.scalarized);
    end if;


    // build primary jacobian (directinoal)
    (jacobian, funcTree) := func(name, jacType, seedCandidates, partialCandidates, part.equations, knowns, part.strongComponents, funcTree, kind ==  NBPartition.Kind.INI);

    // conditionally build adjoint jacobian
    if Flags.getConfigString(Flags.GENERATE_DYNAMIC_JACOBIAN) == "adjoint" and Util.isSome(jacobian) then
      jacobianUnwrap := Util.getOption(jacobian);
      inlined_comps := StrongComponent.inlinePDerTemporaries(BackendDAE.getComponents(jacobianUnwrap));
      jacobianWrap := Jacobian.JACOBIAN(
        name              = name,
        jacType           = jacType,
        varData           = BackendDAE.getVarData(jacobianUnwrap),
        comps             = inlined_comps,
        sparsityPattern   = getSparsityPattern(jacobianUnwrap),
        sparsityColoring  = getSparsityColoring(jacobianUnwrap)
      );

      // Use existing symbolic transpose helper (works for both normal + parameter Jacobian)
      jacobianAdjoint := jacobianSymbolicAdjointFromSymbolic(
        jacobianWrap,
        part.strongComponents,
        BackendDAE.getVarData(jacobianUnwrap),
        seedCandidates,
        partialCandidates,
        jacType,
        name
      );
    end if;

    part.association := Partition.Association.CONTINUOUS(kind, jacobian, jacobianAdjoint);

    if Flags.isSet(Flags.JAC_DUMP) then
      print(Partition.Partition.toString(part, 2));
    end if;
  end partJacobian;

  function jacobianSymbolic extends Module.jacobianInterface;
  protected
    list<StrongComponent> comps, diffed_comps;
    Pointer<list<Pointer<Variable>>> seed_vars_ptr = Pointer.create({});
    Pointer<list<Pointer<Variable>>> pDer_vars_ptr = Pointer.create({});
    UnorderedMap<ComponentRef,ComponentRef> diff_map = UnorderedMap.new<ComponentRef>(ComponentRef.hash, ComponentRef.isEqual);
    Differentiate.DifferentiationArguments diffArguments;
    Pointer<Integer> idx = Pointer.create(0);

    list<Pointer<Variable>> all_vars, unknown_vars, aux_vars, alias_vars, depend_vars, res_vars, tmp_vars, seed_vars;
    BVariable.VarData varDataJac;
    SparsityPattern sparsityPattern;
    SparsityColoring sparsityColoring;

    BVariable.checkVar func = getTmpFilterFunction(jacType);

    array<StrongComponent> inlined_comps;
  algorithm
    if Util.isSome(strongComponents) then
      // filter all discrete strong components and differentiate the others
      // todo: mixed algebraic loops should be here without the discrete subsets
      comps := list(comp for comp guard(not StrongComponent.isDiscrete(comp)) in Util.getOption(strongComponents));
      print("Differentiating " + intString(listLength(comps)) + " strong components.\n");
    else
      Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because no strong components were given!"});
    end if;

    // create seed vars
    VariablePointers.mapPtr(seedCandidates, function makeVarTraverse(name = name, vars_ptr = seed_vars_ptr, map = diff_map, makeVar = BVariable.makeSeedVar, init = init));

    // create pDer vars (also filters out discrete vars)
    (res_vars, tmp_vars) := List.splitOnTrue(VariablePointers.toList(partialCandidates), func);
    (tmp_vars, _) := List.splitOnTrue(tmp_vars, function BVariable.isContinuous(init = init));

    for v in res_vars loop makeVarTraverse(v, name, pDer_vars_ptr, diff_map, function BVariable.makePDerVar(isTmp = false), init = init); end for;
    res_vars := Pointer.access(pDer_vars_ptr);

    pDer_vars_ptr := Pointer.create({});
    for v in tmp_vars loop makeVarTraverse(v, name, pDer_vars_ptr, diff_map, function BVariable.makePDerVar(isTmp = true), init = init); end for;
    tmp_vars := Pointer.access(pDer_vars_ptr);

    // Build differentiation argument structure
    diffArguments := Differentiate.DIFFERENTIATION_ARGUMENTS(
      diffCref        = ComponentRef.EMPTY(),   // no explicit cref necessary, rules are set by diff map
      new_vars        = {},
      diff_map        = SOME(diff_map),         // seed and temporary cref map
      diffType        = NBDifferentiate.DifferentiationType.JACOBIAN,
      funcTree        = funcTree,
      scalarized      = seedCandidates.scalarized
    );

    //print("start\n" + Differentiate.DifferentiationArguments.toString(diffArguments) + "\n");

    // differentiate all strong components
    (diffed_comps, diffArguments) := Differentiate.differentiateStrongComponentList(comps, diffArguments, idx, name, getInstanceName());
    funcTree := diffArguments.funcTree;

    // collect var data (most of this can be removed)
    unknown_vars  := listAppend(res_vars, tmp_vars);
    all_vars      := unknown_vars;  // add other vars later on

    seed_vars     := Pointer.access(seed_vars_ptr);
    aux_vars      := seed_vars;     // add other auxiliaries later on
    alias_vars    := {};
    depend_vars   := {};

    varDataJac := BVariable.VAR_DATA_JAC(
      variables     = VariablePointers.fromList(all_vars),
      unknowns      = VariablePointers.fromList(unknown_vars),
      knowns        = knowns,
      auxiliaries   = VariablePointers.fromList(aux_vars),
      aliasVars     = VariablePointers.fromList(alias_vars),
      diffVars      = partialCandidates,
      dependencies  = VariablePointers.fromList(depend_vars),
      resultVars    = VariablePointers.fromList(res_vars),
      tmpVars       = VariablePointers.fromList(tmp_vars),
      seedVars      = VariablePointers.fromList(seed_vars)
    );

    (sparsityPattern, sparsityColoring) := SparsityPattern.create(seedCandidates, partialCandidates, strongComponents, jacType);

    jacobian := SOME(Jacobian.JACOBIAN(
      name              = name,
      jacType           = jacType,
      varData           = varDataJac,
      comps             = listArray(diffed_comps),
      sparsityPattern   = sparsityPattern,
      sparsityColoring  = sparsityColoring
    ));

    // // use jacobian to generate adjoint jacobian if requested
    // if Flags.getConfigString(Flags.GENERATE_DYNAMIC_JACOBIAN) == "adjoint" then
    //   // inline componentes to avoid issues with pDer temporaries (only when temps exist)
    //   inlined_comps := StrongComponent.inlinePDerTemporaries(listArray(diffed_comps));

    //   jacobian := SOME(Jacobian.JACOBIAN(
    //   name              = name,
    //   jacType           = jacType,
    //   varData           = varDataJac,
    //   comps             = inlined_comps,
    //   sparsityPattern   = sparsityPattern,
    //   sparsityColoring  = sparsityColoring
    //   ));

    //   jacobian := jacobianSymbolicAdjointFromSymbolic(Util.getOption(jacobian), strongComponents, varDataJac, seedCandidates, partialCandidates, jacType, name);
    // end if;
  end jacobianSymbolic;

  function jacobianSymbolicParameters
    "Parameter Jacobian: seeds = parameters, partials = usual residual/state-derivative vars.
     Produces d(f)/dp (where f are residuals producing x' or algebraic residuals)."
    extends Module.jacobianInterface;
  protected
    list<StrongComponent> comps, diffed_comps;
    Pointer<list<Pointer<Variable>>> seed_vars_ptr = Pointer.create({});
    Pointer<list<Pointer<Variable>>> pDer_vars_ptr = Pointer.create({});
    UnorderedMap<ComponentRef,ComponentRef> diff_map = UnorderedMap.new<ComponentRef>(ComponentRef.hash, ComponentRef.isEqual);
    Differentiate.DifferentiationArguments diffArguments;
    Pointer<Integer> idx = Pointer.create(0);

    list<Pointer<Variable>> all_vars, unknown_vars, aux_vars, alias_vars, depend_vars, res_vars, tmp_vars, seed_vars, param_vars;
    BVariable.VarData varDataJac;
    SparsityPattern sparsityPattern;
    SparsityColoring sparsityColoring;

    BVariable.checkVar tmpFilter = getTmpFilterFunction(jacType);
    array<StrongComponent> inlined_comps;
  algorithm
    if Util.isSome(strongComponents) then
      comps := list(c for c guard(not StrongComponent.isDiscrete(c)) in Util.getOption(strongComponents));
    else
      Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " param jacobian: missing strong components."}); fail();
    end if;

    // 1. Collect parameters from knowns (or all vars if needed)
    param_vars := list(v for v guard (BVariable.isParam(v)) in VariablePointers.toList(knowns));

    for v in param_vars loop
      makeParamSeedVarTraverse(v, name, seed_vars_ptr, diff_map);
    end for;
    seed_vars := Pointer.access(seed_vars_ptr);

    // 3. Build pDer variables exactly like normal jacobian (rows = residual/state-derivatives)
    (res_vars, tmp_vars) := List.splitOnTrue(VariablePointers.toList(partialCandidates), tmpFilter);
    (tmp_vars, _) := List.splitOnTrue(tmp_vars, function BVariable.isContinuous(init = init));

    for v in res_vars loop
      makeVarTraverse(v, name, pDer_vars_ptr, diff_map, function BVariable.makePDerVar(isTmp = false), init);
    end for;
    res_vars := Pointer.access(pDer_vars_ptr);

    pDer_vars_ptr := Pointer.create({});
    for v in tmp_vars loop
      makeVarTraverse(v, name, pDer_vars_ptr, diff_map, function BVariable.makePDerVar(isTmp = true), init);
    end for;
    tmp_vars := Pointer.access(pDer_vars_ptr);

    // 4. Diff arguments (JACOBIAN mode with param seeds)
    diffArguments := Differentiate.DIFFERENTIATION_ARGUMENTS(
      diffCref        = ComponentRef.EMPTY(),
      new_vars        = {},
      diff_map        = SOME(diff_map),
      diffType        = NBDifferentiate.DifferentiationType.JACOBIAN,
      funcTree        = funcTree,
      scalarized      = seedCandidates.scalarized   // reuse flag (seedCandidates passed in call can be dummy)
    );

    (diffed_comps, diffArguments) := Differentiate.differentiateStrongComponentList(comps, diffArguments, idx, name, getInstanceName());
    funcTree := diffArguments.funcTree;

    // 5. Assemble VarData (rows = residuals, columns = params)
    unknown_vars  := listAppend(res_vars, tmp_vars);
    all_vars      := unknown_vars;
    aux_vars      := seed_vars;
    alias_vars    := {};
    depend_vars   := {};

    varDataJac := BVariable.VAR_DATA_JAC(
      variables     = VariablePointers.fromList(all_vars),
      unknowns      = VariablePointers.fromList(unknown_vars),
      knowns        = knowns,
      auxiliaries   = VariablePointers.fromList(aux_vars),
      aliasVars     = VariablePointers.fromList(alias_vars),
      diffVars      = partialCandidates,
      dependencies  = VariablePointers.fromList(depend_vars),
      resultVars    = VariablePointers.fromList(res_vars),
      tmpVars       = VariablePointers.fromList(tmp_vars),
      seedVars      = VariablePointers.fromList(seed_vars)      // parameters
    );

    // 6. Sparsity pattern: seeds = params, partials = original unknowns
    (sparsityPattern, sparsityColoring) := SparsityPattern.create(
      VariablePointers.fromList(param_vars, partialCandidates.scalarized),
      partialCandidates,
      strongComponents,
      jacType
    );

    jacobian := SOME(BackendDAE.JACOBIAN(
      name              = name + "_PAR",
      jacType           = jacType,
      varData           = varDataJac,
      comps             = listArray(diffed_comps),
      sparsityPattern   = sparsityPattern,
      sparsityColoring  = sparsityColoring
    ));

    // use jacobian to generate adjoint jacobian if requested
    if Flags.getConfigString(Flags.GENERATE_DYNAMIC_JACOBIAN) == "parameteradjoint" then
      // inline componentes to avoid issues with pDer temporaries
      inlined_comps := StrongComponent.inlinePDerTemporaries(listArray(diffed_comps));

      if Flags.isSet(Flags.JAC_DUMP) then
        // inlined components to string and print
        print("Inlined components for parameter adjoint jacobian:\n");
        print(List.toString(arrayList(inlined_comps), function NBStrongComponent.toString(index = -1)) + "\n");
      end if;

      jacobian := SOME(Jacobian.JACOBIAN(
        name              = name + "_PAR",
        jacType           = jacType,
        varData           = varDataJac,
        comps             = inlined_comps,
        sparsityPattern   = sparsityPattern,
        sparsityColoring  = sparsityColoring
      ));

      jacobian := jacobianSymbolicAdjointFromSymbolic(Util.getOption(jacobian), strongComponents, varDataJac, seedCandidates, partialCandidates, jacType, name);
    end if;
  end jacobianSymbolicParameters;


  protected function allZeros
    input list<Expression> xs;
    output Boolean b;
  algorithm
    b := true;
    for e in xs loop
      if not Expression.isZero(e) then
        b := false;
        break;
      end if;
    end for;
  end allZeros;


  protected function buildJacobianEquationsFromTransposed
    "Constructs new jacobian equations from a transposed coefficient matrix.
    Each row of the transposed matrix becomes an equation:
      newResultVar[i] = sum_j (coeff[i][j] * newSeedVar[j])
    - newResultVars: list of result variable pointers (LHS, one per row)
    - newSeedVars: list of seed variable pointers (RHS, one per column)
    - coeffsT: transposed coefficient matrix (coeffsT[i][j] is coefficient for resultVar[i], seedVar[j])
    Returns: list of new NBEquation.Equation equations."
    input list<Expression> newResultVars;
    input list<Expression> newSeedVars;
    input list<list<Expression>> coeffsT;
    output list<EquationPointer> newEquations;
  protected
    Integer nRows, nCols, i, j;
    VariablePointer resVarPtr, seedVarPtr;
    Expression lhs, rhs, term, seedVar;
    list<Expression> row, terms;
    EquationPointer eq;
  algorithm
    newEquations := {};
    nRows := listLength(coeffsT);
    nCols := if nRows > 0 then listLength(listHead(coeffsT)) else 0;

    for i in 1:nRows loop
      row := listGet(coeffsT, i);
      // lhs := Expression.CREF(BVariable.getVarType(resVarPtr), BVariable.getVarName(resVarPtr));

      terms := {};
      for j in 1:nCols loop
        seedVar := listGet(newSeedVars, j);
        // get the coefficient
        term := listGet(row, j);
        // skip zero coefficients
        if not Expression.isZero(term) then
          // Multiply coefficient by seed variable
          term := Expression.BINARY(
            term,
            Operator.makeMul(Type.REAL()),
            seedVar
          );
          terms := term :: terms;
        end if;
      end for;

      // Build RHS: sum all terms, or 0 if empty
      if listEmpty(terms) then
        rhs := Expression.REAL(0.0);
      else
        rhs := Expression.MULTARY(terms, {}, Operator.makeAdd(Type.REAL()));
      end if;

      // Build the equation: lhs = rhs
      lhs := listGet(newResultVars, i);
      eq := BEquation.Equation.makeAssignment(lhs, rhs, Pointer.create(i-1), "ODE_JAC_ADJ", BEquation.Iterator.EMPTY(), BackendDAE.EquationAttributes.default(NBEquation.EquationKind.CONTINUOUS, false));
      newEquations := eq :: newEquations;
    end for;
    newEquations := listReverse(newEquations);
  end buildJacobianEquationsFromTransposed;


  protected function transposeSeedAndPDerCrefs
    "Given lists of seed CREF expressions and pDer CREF expressions,
    returns the 'transposed' lists with inferred SEED and pDER prefixes:
    - newSeeds: <seedPrefix><baseName> for each original pDer
    - newPders: <pDerPrefix><baseName> for each original seed"
    input list<VariablePointer> seedCrefExprs;
    input list<VariablePointer> pDerCrefExprs;
    output list<Expression> newSeedCrefExprs;
    output list<Expression> newPDerCrefExprs;
    output list<VariablePointer> newSeedPtrList;
    output list<VariablePointer> newPDerPtrList;
  protected
    String seedPrefix, pDerPrefix, baseName, fullName;
    ComponentRef base, newSeed, newPDer;
    VariablePointer newSeedPtr, newPDerPtr;

    Expression e;
    Type ty;
    Integer prefixLen;
  algorithm
    // New seeds: wrap each pDer cref name in seedPrefix
    newSeedCrefExprs := {};
    newSeedPtrList := {};
    for e in pDerCrefExprs loop
      ty := BVariable.getVarType(e);
      base := BVariable.getVarName(e);
      (newSeed, newSeedPtr) := BVariable.makeSeedVar(base, "ODE_JAC_ADJ");
      newSeedCrefExprs := Expression.CREF(ty, newSeed) :: newSeedCrefExprs;
      newSeedPtrList := newSeedPtr :: newSeedPtrList;
    end for;

    // New pDers: wrap each seed cref name in pDerPrefix
    newPDerCrefExprs := {};
    newPDerPtrList := {};
    for e in seedCrefExprs loop
      ty := BVariable.getVarType(e);
      base := BVariable.getVarName(e);
      (newPDer, newPDerPtr) := BVariable.makePDerVar(base, "ODE_JAC_ADJ", false);
      newPDerCrefExprs := Expression.CREF(ty, newPDer) :: newPDerCrefExprs;
      newPDerPtrList := newPDerPtr :: newPDerPtrList;
    end for;

    newPDerCrefExprs := listReverse(newPDerCrefExprs);
    newPDerPtrList := listReverse(newPDerPtrList);
  end transposeSeedAndPDerCrefs;


  protected function findSeedByBase
    input ComponentRef baseCref;
    input list<VariablePointer> seedPtrs;
    output Option<ComponentRef> seedOpt;
  protected
    ComponentRef sCref;
    String baseStr = ComponentRef.toString(baseCref);
    String seedStr;
  algorithm
    seedOpt := NONE();
    for sPtr in seedPtrs loop
      sCref := BVariable.getVarName(sPtr);         // $SEED_….<base>
      seedStr := ComponentRef.toString(sCref);
      // Match if seed ends with ".<base>" or equals <base> (defensive)
      if StringUtil.endsWith(seedStr, "." + baseStr) or seedStr == baseStr then
        seedOpt := SOME(sCref);
        break;
      end if;
    end for;
  end findSeedByBase;

  protected function jacobianSymbolicAdjointFromSymbolic
    "For a JACOBIAN backendDAE: iterate all strong components and for each
    compute the expression results for each seed by setting the seed of
    interest to 1 and all other seeds to 0. Returns a list per equation of the
    substituted expressions (one entry per seed)."
    input BackendDAE jac;
    input Option<array<StrongComponent>> strongComponents;
    input BVariable.VarData varDataJac;
    input VariablePointers seedCandidates;
    input VariablePointers partialCandidates;
    input JacobianType jacType;
    input String name;
    output Option<Jacobian> jacobian;
  protected
    BVariable.VarData vd;
    list<VariablePointer> seedPtrList, pDerPtrList;
    array<StrongComponent> comps, diffed_comps_array;
    list<StrongComponent> diffed_comps = {};
    Integer eqi, s;
    ComponentRef seedVarName;
    Pointer<Equation> eqPtr;
    Expression eqExp, pder, eqCopy, term;
    UnorderedMap<ComponentRef, Expression> replaceMap;
    list<list<Expression>> coeffsT = {}, coeffs = {};
    list<Expression> seedCrefExprs = {}, pDerCrefExprs = {};
    list<Expression> singleEqResults = {};
    list<EquationPointer> newEquations = {};
    StrongComponent diffed_comp;
    SparsityPattern sparsityPattern, oldSparsityPattern;
    SparsityColoring sparsityColoring;
    list<VariablePointer> newSeedPtrList, newPDerPtrList, tmp_;
    VariablePointer pderPtr;


    UnorderedMap<ComponentRef, ComponentRef> mapPartialToNewSeed =
      UnorderedMap.new<ComponentRef>(ComponentRef.hash, ComponentRef.isEqual);
    UnorderedMap<ComponentRef, ComponentRef> mapSeedToNewPDer =
      UnorderedMap.new<ComponentRef>(ComponentRef.hash, ComponentRef.isEqual);
    UnorderedMap<ComponentRef, Integer> seedIndexMap;
    UnorderedMap<ComponentRef, list<ComponentRef>> rowDepMap;
    ComponentRef oldC, newC, rowCref, oldCref, seedCref, baseSeed;
    CrefLst oldDeps, activeSeeds;
    array<Expression> rowArr;

    Integer idxTmp, colIdx, i;
    Boolean updated;
    array<StrongComponent> origComps;
    Option<ComponentRef> seedOpt;
  algorithm  
    // extract varData and seed variable pointers
    vd := BackendDAE.getVarData(jac);
    // adjust field access if your VarData record uses different field name
    seedPtrList := VariablePointers.toList(VarData.getSeeds(vd));
    pDerPtrList := VariablePointers.toList(VarData.getUnknowns(vd));

    // print("seedCandidates:\n");
    // for v in VariablePointers.toList(seedCandidates) loop
    //   print("  " + ComponentRef.toString(BVariable.getVarName(v)) + "\n");
    // end for;

    // // Print partialCandidates
    // print("partialCandidates:\n");
    // for v in VariablePointers.toList(partialCandidates) loop
    //   print("  " + ComponentRef.toString(BVariable.getVarName(v)) + "\n");
    // end for;
    // build seed cref expressions for easy matching: Expression.CREF(cref)
    seedCrefExprs := list(Expression.CREF(Type.REAL(), BVariable.getVarName(s_i)) for s_i in seedPtrList); // length is number of seeds
    // if Flags.isSet(Flags.JAC_DUMP) then
    //   print("Jacobian original seeds:\n");
    //   print(
    //     StringUtil.stringDelimitList(
    //       List.map(seedCrefExprs, Expression.toString),
    //       ", "
    //     ) + "\n"
    //   );
    // end if;
    pDerCrefExprs := list(Expression.CREF(Type.REAL(), BVariable.getVarName(p_i)) for p_i in pDerPtrList); // length is number of equations
    // if Flags.isSet(Flags.JAC_DUMP) then
    //   print("Jacobian original pders:\n");
    //   print(
    //     StringUtil.stringDelimitList(
    //       List.map(pDerCrefExprs, Expression.toString),
    //       ", "
    //     ) + "\n"
    //   );
    // end if;

    // iterate strong components; get array and its length
    comps := BackendDAE.getComponents(jac);
    origComps := listArray(list(c for c guard(not StrongComponent.isDiscrete(c)) in Util.getOption(strongComponents)));
    oldSparsityPattern := getSparsityPattern(jac);

    // For each strong component, extract its coefficients.
    replaceMap := UnorderedMap.new<Expression>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(seedPtrList) + listLength(pDerPtrList)));

    // for sCref in oldSparsityPattern.seed_vars loop
    //   UnorderedMap.add(sCref, Expression.REAL(0.0), replaceMap);
    // end for;
    // Seed variables default to 0.0
    for sPtr in seedPtrList loop
      UnorderedMap.add(BVariable.getVarName(sPtr), Expression.REAL(0.0), replaceMap);
    end for;
    // // pDer variables always 0.0 here
    // for pDerPtr in pDerPtrList loop
    //   UnorderedMap.add(BVariable.getVarName(pDerPtr), Expression.REAL(0.0), replaceMap);
    // end for;


    // Build lookup: seed cref -> column index
    // Needed to place each computed coefficient in the correct column.
    // Use 1-based indices to match listGet semantics.
    seedIndexMap := UnorderedMap.new<Integer>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(seedPtrList)));
    // for j in 1:listLength(seedPtrList) loop
    //   UnorderedMap.add(BVariable.getVarName(listGet(seedPtrList, j)), j, seedIndexMap);
    // end for;
    i := 1;
    for sCref in oldSparsityPattern.seed_vars loop
      UnorderedMap.add(sCref, i, seedIndexMap);
      i := i + 1;
    end for;


    // Build lookup: row (partial/pDer) cref -> list of seed crefs that affect it (row-wise sparsity)
    // just the row wise pattern in a map for fast lookup
    rowDepMap := UnorderedMap.new<CrefLst>(ComponentRef.hash, ComponentRef.isEqual, Util.nextPrime(listLength(pDerPtrList)));
    for tpl in oldSparsityPattern.row_wise_pattern loop
      (oldCref, oldDeps) := tpl;
      UnorderedMap.add(oldCref, oldDeps, rowDepMap);
    end for;

    for eqi in 1:arrayLength(comps) loop
      eqPtr := StrongComponent.getEquationPointer(comps[eqi]);
      eqExp := Equation.getRHS(Pointer.access(eqPtr));
      //eqExp := Equation.getResidualExp(Pointer.access(eqPtr));

      // Identify the row variable (partial/pDer) for this equation
      // rowCref := BVariable.getVarName(listGet(pDerPtrList, eqi));
      rowCref := BVariable.getVarName(StrongComponent.getVarPointer(origComps[eqi]));


      // Get only the active seeds for this row from sparsity; if unknown, assume none
      activeSeeds := if UnorderedMap.contains(rowCref, rowDepMap) then UnorderedMap.getOrFail(rowCref, rowDepMap) else {};
      print(intString(listLength(activeSeeds)) + " active seeds for equation " + intString(eqi) + "\n");
      // initialize with dense zeros
      //rowArr := arrayCreate(listLength(seedPtrList), Expression.REAL(0.0));
      rowArr := arrayCreate(listLength(oldSparsityPattern.seed_vars), Expression.REAL(0.0));

      // Toggle only the active seeds one-by-one: seed := 1.0, evaluate, reset to 0.0
      for baseSeed in activeSeeds loop
        colIdx := UnorderedMap.getSafe(baseSeed, seedIndexMap, sourceInfo());

        // Find corresponding $SEED cref to toggle in RHS
        // If none found, skip (e.g. seed pruned in forward Jacobian)
        seedOpt := findSeedByBase(baseSeed, seedPtrList);
        if Util.isNone(seedOpt) then
          continue;
        end if;
        seedCref := Util.getOption(seedOpt);

        // Set current seed to 1.0
        _ := UnorderedMap.tryUpdate(seedCref, Expression.REAL(1.0), replaceMap);

        // Substitute on a fresh copy and simplify
        eqCopy := eqExp;
        eqCopy := replaceCrefsInExp(eqCopy, replaceMap);
        eqCopy := SimplifyExp.simplify(eqCopy);

        // Place result in the correct column, leave others at 0.0
        rowArr[colIdx] := eqCopy;

        // Reset current seed to 0.0 for next iteration
        _ := UnorderedMap.tryUpdate(seedCref, Expression.REAL(0.0), replaceMap);
      end for;

      // Append dense row to coefficient matrix
      coeffs := arrayList(rowArr) :: coeffs;
    end for;

    // singleEqResults := {};
    // // set each seed to 1 once
    // for s in 1:listLength(seedPtrList) loop
    //   seedVarName := BVariable.getVarName(listGet(seedPtrList, s));
    //   // set current seed to 1.0
    //   updated := UnorderedMap.tryUpdate(seedVarName, Expression.REAL(1.0), replaceMap);
    //   if not updated then
    //     Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed to set seed value in map for adjoint jacobian."});
    //   end if;

    //   eqCopy := eqExp;
    //   eqCopy := replaceCrefsInExp(eqCopy, replaceMap);
    //   eqCopy := SimplifyExp.simplify(eqCopy);

    //   // term := Expression.BINARY(
    //   //     eqCopy,
    //   //     Operator.makeMul(Type.REAL()),
    //   //     BVariable.toExpression(listGet(seedPtrList, eqi)) // because of the transpose, use eqi here
    //   // );

    //   singleEqResults := eqCopy :: singleEqResults;

    //   // reset seed to 0.0
    //   updated := UnorderedMap.tryUpdate(seedVarName, Expression.REAL(0.0), replaceMap);
    //   if not updated then
    //     Error.addMessage(Error.INTERNAL_ERROR, {getInstanceName() + " failed to reset seed value in map for adjoint jacobian."});
    //   end if;
    // end for;
    // coeffs := singleEqResults :: coeffs;
    // end for;
    // transpose the coefficient matrix
    coeffsT := List.transposeList(coeffs);


    // if Flags.isSet(Flags.JAC_DUMP) then
    //   print("Jacobian adjoint coefficient matrix (transposed):\n");
    //   for row in coeffsT loop
    //     for e in row loop
    //       print(Expression.toString(e) + " ");
    //     end for;
    //     print("\n");
    //   end for;
    // end if;

    // now we need new seedPtrList and pDerPtrList for the adjoint jacobian
    // with number of seeds = number of columns in coeffsT
    // and number of equations = number of rows in coeffsT
    (seedCrefExprs, pDerCrefExprs, newSeedPtrList, newPDerPtrList) := transposeSeedAndPDerCrefs(VariablePointers.toList(seedCandidates), VariablePointers.toList(partialCandidates));

    // if Flags.isSet(Flags.JAC_DUMP) then
    //   print("Jacobian transposed seeds:\n");
    //   print(
    //     StringUtil.stringDelimitList(
    //       List.map(seedCrefExprs, Expression.toString),
    //       ", "
    //     ) + "\n"
    //   );
    // end if;
    // if Flags.isSet(Flags.JAC_DUMP) then
    //   print("Jacobian transposed pders:\n");
    //   print(
    //     StringUtil.stringDelimitList(
    //       List.map(pDerCrefExprs, Expression.toString),
    //       ", "
    //     ) + "\n"
    //   );
    // end if;

    // the rows of coeffsT are the new equations, each element per row gets its own seed
    // the columns of coeffsT get the same seed
    newEquations := buildJacobianEquationsFromTransposed(pDerCrefExprs, seedCrefExprs, coeffsT);

    // // print new equations
    // print("Jacobian adjoint equations:\n");
    // for eqPtr in newEquations loop
    //   print(NBEquation.Equation.toString(Pointer.access(eqPtr)) + "\n");
    // end for;

    // ToDo: handle other component types and take solve status from original component
    for i in 1:listLength(newEquations) loop
      pderPtr := listGet(newPDerPtrList, i);
      diffed_comp := StrongComponent.SINGLE_COMPONENT(
        pderPtr,
        listGet(newEquations, i),
        StrongComponent.getStatus(comps[i])
      );
      diffed_comps := diffed_comp :: diffed_comps;
    end for;
    diffed_comps_array := listArray(diffed_comps);


    // print("Jacobian diffed comps:\n");
    // for comp in diffed_comps_array loop
    //   print(StrongComponent.toString(comp) + "\n");
    // end for;
    // print("##################\n");
    
    // (sparsityPattern, sparsityColoring) := SparsityPattern.create(seedCandidates, partialCandidates, SOME(listArray(listReverse(newEquationsSC))), jacType);
    // assume full dependency for now (lazy)


    // original partials = pDerPtrList to new seeds = newSeedPtrList
    // idxTmp := 1;
    // for p in pDerPtrList loop
    //   oldC := BVariable.getVarName(p);
    //   // seedCrefExprs list corresponds to new seed expressions (constructed earlier)
    //   newC := BVariable.getVarName(listGet(newSeedPtrList, idxTmp)); // new seed crefs
    //   UnorderedMap.add(oldC, newC, mapPartialToNewSeed);
    //   idxTmp := idxTmp + 1;
    // end for;

    // 1) old partials -> new seeds
    tmp_ := listReverse(newSeedPtrList);
    i := 1;
    for oldC in oldSparsityPattern.partial_vars loop
      if i <= listLength(tmp_) then
        newC := BVariable.getVarName(listGet(tmp_, i));
        UnorderedMap.add(oldC, newC, mapPartialToNewSeed);
      end if;
      i := i + 1;
    end for;

    print("Map original partials to new seeds:\n");
    print(UnorderedMap.toString(mapPartialToNewSeed, ComponentRef.toString, ComponentRef.toString) + "\n");


    // // original seeds = seedPtrList to new pDers = newPDerPtrList
    // idxTmp := 1;
    // for sPtr in listReverse(seedPtrList) loop
    //   oldC := BVariable.getVarName(sPtr);
    //   newC := BVariable.getVarName(listGet(newPDerPtrList, idxTmp));
    //   UnorderedMap.add(oldC, newC, mapSeedToNewPDer);
    //   idxTmp := idxTmp + 1;
    // end for;

    // 2) old seeds -> new pDers
    i := 1;
    for oldC in oldSparsityPattern.seed_vars loop
      if i <= listLength(newPDerPtrList) then
        newC := BVariable.getVarName(listGet(newPDerPtrList, i));
        UnorderedMap.add(oldC, newC, mapSeedToNewPDer);
      end if;
      i := i + 1;
    end for;

    print("Map original seeds to new pDers:\n");
    print(UnorderedMap.toString(mapSeedToNewPDer, ComponentRef.toString, ComponentRef.toString) + "\n");

    (sparsityPattern, sparsityColoring) :=
      SparsityPattern.transposeRenamed(
        getSparsityPattern(jac),
        mapPartialToNewSeed,
        mapSeedToNewPDer,
        BackendDAE.getJacType(jac)
      );
    // (sparsityPattern, sparsityColoring) := SparsityPattern.transpose(getSparsityPattern(jac), BackendDAE.getJacType(jac));

    vd := BVariable.VarData.setDiffVars(vd, partialCandidates);
    vd := BVariable.VarData.setUnknowns(vd, VariablePointers.fromList(newPDerPtrList));
    vd := BVariable.VarData.setResultVars(vd, VariablePointers.fromList(newPDerPtrList));
    vd := BVariable.VarData.setSeedVars(vd, VariablePointers.fromList(newSeedPtrList));

    jacobian := SOME(Jacobian.JACOBIAN(
      name              = name,
      jacType           = jacType,
      varData           = vd,
      comps             = diffed_comps_array,
      sparsityPattern   = sparsityPattern,
      sparsityColoring  = sparsityColoring
    ));


    print("Jacobian adjoint:\n" + NBJacobian.toString(Util.getOption(jacobian), " ") + "\n");
    print("Sparsity pattern adjoint:\n" + SparsityPattern.toString(sparsityPattern) + "\n");
    print("Sparsity coloring adjoint:\n" + SparsityColoring.toString(sparsityColoring) + "\n");

    if Flags.isSet(Flags.JAC_DUMP) then
      print("Jacobian adjoint:\n" + NBJacobian.toString(Util.getOption(jacobian), " ") + "\n");
      print("Sparsity pattern adjoint:\n" + SparsityPattern.toString(sparsityPattern) + "\n");
      print("Sparsity coloring adjoint:\n" + SparsityColoring.toString(sparsityColoring) + "\n");
      //print("Jacobian adjoint VarData:\n" + BVariable.VarData.toStringVerbose(vd, true) + "\n");
    end if;
  end jacobianSymbolicAdjointFromSymbolic;

  function replaceIfSeed
    input output Expression e;
    input list<Expression> seedList;
    input Expression repl;
  protected
    String s;
  algorithm
    if Expression.isCref(e) then
      s := Expression.toString(e);
      for targetStr in seedList loop
        if s == Expression.toString(targetStr) then
          e := repl;
          break;
        end if;
      end for;
    end if;
  end replaceIfSeed;

  protected function replaceSeedsInExpWithSeed
    "Replace any CREF in `exp` that matches one of `seedCrefExprs` (by Expression.toString)
     with `seedExpr` and return the replaced expression."
    input Expression exp;
    input list<Expression> seedCrefExprs;
    input Expression seedExpr;
    output Expression outExp;
  protected
    String targetStr;
  algorithm
    // map callback: if node is a cref and its string matches one of the seeds -> replace
    outExp := Expression.map(exp, function replaceIfSeed(seedList = seedCrefExprs, repl = seedExpr));
  end replaceSeedsInExpWithSeed;


  protected function replaceCrefsInEquationRhs
    "Replace crefs only in the RHS of the given equation pointer and return a new EquationPointer.
    Assumes NBEquation.Equation exposes getLhsExp/getRhsExp/getIndex/getLabel/getIterator/getAttributes (adjust names if different)."
    input EquationPointer eqPtr;
    input list<Expression> seedCrefExprs;
    input Expression seedExpr;
    input Integer i                                     "Index for new equation";
    output EquationPointer newEqPtr;
  protected
    Equation eq;
    Expression lhs, rhs, newRhs;
    Integer idx;
    String label;
    BEquation.Iterator iter;
    BackendDAE.EquationAttributes attrs;
  algorithm
    eq := Pointer.access(eqPtr);

    // try to extract LHS/RHS; if not available fall back to residual (lhs := residual, rhs := 0)
    lhs := BEquation.Equation.getLHS(eq);
    rhs := BEquation.Equation.getRHS(eq);

    // replace crefs only in rhs
    newRhs := replaceSeedsInExpWithSeed(rhs, seedCrefExprs, seedExpr);

    // preserve metadata if available
    // ty := BEquation.Equation.getType(eq);
    // source := BEquation.Equation.getSource(eq);
    // attrs := BEquation.Equation.getAttributes(eq);

    // rebuild assignment: lhs = newRhs (use same create function as elsewhere)
    newEqPtr := BEquation.Equation.makeAssignment(
      lhs, newRhs, 
      Pointer.create(i-1), 
      "ODE_JAC_ADJ", 
      BEquation.Iterator.EMPTY(), 
      BackendDAE.EquationAttributes.default(NBEquation.EquationKind.CONTINUOUS, false));
  end replaceCrefsInEquationRhs;


  protected function getSparsityPattern
    input BackendDAE jac;
    output SparsityPattern sparsityPattern;
  algorithm
    sparsityPattern := match jac
      case BackendDAE.JACOBIAN(_, _, _, _, sparsityPattern, _) then sparsityPattern;
      else algorithm
        Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because the given backendDAE is not a JACOBIAN."});
      then fail();
    end match;
  end getSparsityPattern;

  protected function getSparsityColoring
    input BackendDAE jac;
    output SparsityColoring sparsityColoring;
  algorithm
    sparsityColoring := match jac
      case BackendDAE.JACOBIAN(_, _, _, _, _, sparsityColoring) then sparsityColoring;
      else algorithm
        Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because the given backendDAE is not a JACOBIAN."});
      then fail();
    end match;
  end getSparsityColoring;


  protected function jacobianSymbolicAdjointFromSymbolicSeeds
    "For a JACOBIAN backendDAE: iterate all strong components and for each
    compute the expression results for each seed by setting the seed of
    interest to 1 and all other seeds to 0. Returns a list per equation of the
    substituted expressions (one entry per seed)."
    input BackendDAE jac;
    input Option<array<StrongComponent>> strongComponents;
    input BVariable.VarData varDataJac;
    input VariablePointers seedCandidates;
    input VariablePointers partialCandidates;
    input JacobianType jacType;
    input String name;
    output Option<Jacobian> jacobian;
  protected
    BVariable.VarData vd;
    list<VariablePointer> seedPtrList, pDerPtrList;
    array<StrongComponent> comps, diffed_comps_array;
    list<StrongComponent> diffed_comps = {};
    Integer eqi, s;
    ComponentRef seedVarName;
    EquationPointer eqPtr;
    Expression currentSeedExpr;
    UnorderedMap<ComponentRef, Expression> replaceMap;
    list<Expression> seedCrefExprs = {}, pDerCrefExprs = {};
    list<EquationPointer> results = {};
    StrongComponent diffed_comp;
    SparsityPattern sparsityPattern;
    SparsityColoring sparsityColoring;
  algorithm  
    // extract varData and seed variable pointers
    vd := BackendDAE.getVarData(jac);
    // adjust field access if your VarData record uses different field name
    seedPtrList := VariablePointers.toList(VarData.getSeeds(vd));
    pDerPtrList := VariablePointers.toList(VarData.getUnknowns(vd));
    // build seed cref expressions for easy matching: Expression.CREF(cref)
    seedCrefExprs := list(Expression.CREF(Type.REAL(), BVariable.getVarName(s_i)) for s_i in seedPtrList);
    pDerCrefExprs := list(Expression.CREF(Type.REAL(), BVariable.getVarName(p_i)) for p_i in pDerPtrList);

    print("exprs: " + List.toString(seedCrefExprs, Expression.toString) + "\n");
    // iterate strong components; get array and its length
    comps := BackendDAE.getComponents(jac);

    // For each strong component, set seeds.
    for eqi in 1:arrayLength(comps) loop
      currentSeedExpr := listGet(seedCrefExprs, eqi);
      print("Current equation: " + BEquation.Equation.toString(Pointer.access(StrongComponent.getEquationPointer(comps[eqi]))) + "\n");
      print("Current seed: " + Expression.toString(currentSeedExpr) + "\n");
      // For each seed build a replacement map: seed_s -> 1, others -> 0
      for s in 1:listLength(seedPtrList) loop
        replaceMap := UnorderedMap.new<NBackendDAE.Expression>(NBackendDAE.ComponentRef.hash, NBackendDAE.ComponentRef.isEqual);
        seedVarName := BVariable.getVarName(listGet(seedPtrList, s));
        UnorderedMap.add(seedVarName, currentSeedExpr, replaceMap);
      end for;

      eqPtr := StrongComponent.getEquationPointer(comps[eqi]);
      //eqPtr := replaceCrefsInEquationRhs(eqPtr, replaceMap, eqi);
      eqPtr := replaceCrefsInEquationRhs(eqPtr, seedCrefExprs, currentSeedExpr, eqi);
      //eqPtr := SimplifyExp.simplify(eqPtr);

      results := eqPtr :: results;
      print("Resulting equation: " + BEquation.Equation.toString(Pointer.access(eqPtr)) + "\n");
    end for;

    // ToDo: handle other component types and take solve status from original component
    for i in 1:listLength(results) loop
      diffed_comp := StrongComponent.SINGLE_COMPONENT(
        listGet(pDerPtrList, i),
        listGet(results, i),
        NBSolve.Status.EXPLICIT
      );
      diffed_comps := diffed_comp :: diffed_comps;
    end for;
    diffed_comps_array := listArray(diffed_comps);
    
    // (sparsityPattern, sparsityColoring) := SparsityPattern.create(seedCandidates, partialCandidates, SOME(listArray(listReverse(newEquationsSC))), jacType);
    // assume full dependency for now (lazy)
    //(sparsityPattern, sparsityColoring) := SparsityPattern.lazy(seedCandidates, partialCandidates, SOME(diffed_comps_array), jacType);

    jacobian := SOME(Jacobian.JACOBIAN(
      name              = name,
      jacType           = jacType,
      varData           = varDataJac,
      comps             = diffed_comps_array,
      sparsityPattern   = getSparsityPattern(jac),
      sparsityColoring  = getSparsityColoring(jac)
    ));

    if Flags.isSet(Flags.JAC_DUMP) then
      print("Jacobian adjoint:\n" + NBJacobian.toString(Util.getOption(jacobian), " ") + "\n");
    end if;
  end jacobianSymbolicAdjointFromSymbolicSeeds;

  function jacobianNumeric "still creates sparsity pattern"
    extends Module.jacobianInterface;
  protected
    VarData varDataJac;
    SparsityPattern sparsityPattern;
    SparsityColoring sparsityColoring;
    list<Pointer<Variable>> res_vars, tmp_vars;
    BVariable.checkVar func = getTmpFilterFunction(jacType);
  algorithm
    (res_vars, tmp_vars) := List.splitOnTrue(VariablePointers.toList(partialCandidates), func);
    (tmp_vars, _) := List.splitOnTrue(tmp_vars, function BVariable.isContinuous(init = init));

    varDataJac := BVariable.VAR_DATA_JAC(
      variables     = VariablePointers.fromList({}),
      unknowns      = partialCandidates,
      knowns        = VariablePointers.fromList({}),
      auxiliaries   = VariablePointers.fromList({}),
      aliasVars     = VariablePointers.fromList({}),
      diffVars      = VariablePointers.fromList({}),
      dependencies  = VariablePointers.fromList({}),
      resultVars    = VariablePointers.fromList(res_vars),
      tmpVars       = VariablePointers.fromList(tmp_vars),
      seedVars      = seedCandidates
    );

    (sparsityPattern, sparsityColoring) := SparsityPattern.create(seedCandidates, partialCandidates, strongComponents, jacType);

    jacobian := SOME(Jacobian.JACOBIAN(
      name              = name + "ADJ",
      jacType           = jacType,
      varData           = varDataJac,
      comps             = listArray({}),
      sparsityPattern   = sparsityPattern,
      sparsityColoring  = sparsityColoring
    ));
  end jacobianNumeric;

  function jacobianNone
    extends Module.jacobianInterface;
  algorithm
    jacobian := NONE();
  end jacobianNone;

  function getTmpFilterFunction
    " - ODE filter by state derivative / algebraic
      - LS/NLS/DAE filter by residual / inner"
    input JacobianType jacType;
    output BVariable.checkVar func;
  algorithm
    func := match jacType
      case JacobianType.ODE then BVariable.isStateDerivative;
      case JacobianType.DAE then BVariable.isResidual;
      case JacobianType.LS  then BVariable.isResidual;
      case JacobianType.NLS then BVariable.isResidual;
      else algorithm
        Error.addMessage(Error.INTERNAL_ERROR,{getInstanceName() + " failed because jacobian type is not known: " + jacobianTypeString(jacType)});
      then fail();
    end match;
  end getTmpFilterFunction;

  function makeVarTraverse
    input Pointer<Variable> var_ptr;
    input String name;
    input Pointer<list<Pointer<Variable>>> vars_ptr;
    input UnorderedMap<ComponentRef,ComponentRef> map;
    input Func makeVar;
    input Boolean init;

    partial function Func
      input output ComponentRef cref;
      input String name;
      output Pointer<Variable> diff_ptr;
    end Func;
  protected
    Variable var = Pointer.access(var_ptr);
    ComponentRef diff, parent_name, diff_parent_name;
    Pointer<Variable> diff_ptr, parent, diff_parent;
  algorithm
    // only create seed or pDer var if it is continuous
    if BVariable.isContinuous(var_ptr, init) then
      // make the new differentiated variable itself
      (diff, diff_ptr) := makeVar(var.name, name);
      // add $<new>.x variable pointer to the variables
      Pointer.update(vars_ptr, diff_ptr :: Pointer.access(vars_ptr));
      // add x -> $<new>.x to the map for later lookup
      UnorderedMap.add(var.name, diff, map);

      // differentiate parent and add to map
      _ := match BVariable.getParent(var_ptr)
        case SOME(parent) algorithm
          parent_name := BVariable.getVarName(parent);
          diff_parent := match UnorderedMap.get(parent_name, map)
            case SOME(diff_parent_name) then BVariable.getVarPointer(diff_parent_name, sourceInfo());
            else algorithm
              (diff_parent_name, _) := makeVar(parent_name, name);
              UnorderedMap.add(parent_name, diff_parent_name, map);
            then BVariable.getVarPointer(diff_parent_name, sourceInfo());
          end match;

          // add the child to the list of children
          BVariable.addRecordChild(diff_parent, diff_ptr);
          // set the parent of the child
          diff_ptr := BVariable.setParent(diff_ptr, diff_parent);
        then ();

        else ();
      end match;
    end if;
  end makeVarTraverse;


  function makeParamSeedVarTraverse
    "Create a seed variable for a parameter (do NOT check continuity)."
    input Pointer<Variable> var_ptr;
    input String name;
    input Pointer<list<Pointer<Variable>>> vars_ptr;
    input UnorderedMap<ComponentRef,ComponentRef> map;
  protected
    Variable var = Pointer.access(var_ptr);
    ComponentRef diff, parent_name, diff_parent_name;
    Pointer<Variable> diff_ptr, parent, diff_parent;
  algorithm
    // always create a seed for parameters
    (diff, diff_ptr) := BVariable.makeSeedVar(var.name, name);
    Pointer.update(vars_ptr, diff_ptr :: Pointer.access(vars_ptr));
    UnorderedMap.add(var.name, diff, map);

    // keep parent relation (copy from makeVarTraverse but without continuity guard)
    _ := match BVariable.getParent(var_ptr)
      case SOME(parent) algorithm
        parent_name := BVariable.getVarName(parent);
        diff_parent := match UnorderedMap.get(parent_name, map)
          case SOME(diff_parent_name) then BVariable.getVarPointer(diff_parent_name, sourceInfo());
          else algorithm
            (diff_parent_name, _) := BVariable.makeSeedVar(parent_name, name);
            UnorderedMap.add(parent_name, diff_parent_name, map);
          then BVariable.getVarPointer(diff_parent_name, sourceInfo());
        end match;
        BVariable.addRecordChild(diff_parent, diff_ptr);
        diff_ptr := BVariable.setParent(diff_ptr, diff_parent);
      then ();
      else ();
    end match;
  end makeParamSeedVarTraverse;

  protected function replaceCrefsInExp
    "Replaces all occurrences of crefs in an expression according to the given map."
    input output Expression exp;
    input UnorderedMap<ComponentRef, Expression> replaceMap;
  algorithm
    exp := Expression.map(exp, function replaceCrefInExp1(replaceMap = replaceMap));
  end replaceCrefsInExp;

  protected function replaceCrefInExp1
    input output Expression exp;
    input UnorderedMap<ComponentRef, Expression> replaceMap;
  protected
    ComponentRef cref;
  algorithm
    if Expression.isCref(exp) then
      cref := Expression.toCref(exp);
      if UnorderedMap.contains(cref, replaceMap) then
        exp := UnorderedMap.getOrFail(cref, replaceMap);
      end if;
    end if;
  end replaceCrefInExp1;

  protected function makeAddExp
    input Expression e1;
    input Expression e2;
    output Expression res;
  algorithm
    res := Expression.BINARY(e1, Operator.makeAdd(Type.REAL()), e2);
  end makeAddExp;

  annotation(__OpenModelica_Interface="backend");
end NBJacobian;
