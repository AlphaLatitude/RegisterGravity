import Lean

/-!
# `#premises`: the premise ledger, checked at build time

`#premises thm₁ thm₂ …` reads the type of each theorem and lists its hypotheses.  Every hypothesis
(a binder whose type is a proposition) must be a definition of `Sources.lean`, that is, a constant
in the namespace `Register.Sources`, or the class `NeZero` or `Nonempty`; and every object (a binder whose type is
not a proposition) must have a type whose head, and the heads of the domains of its function
types, are among the object types listed in `allowedObjects` below.  Anything else fails the build
with an error that names the binder.  The output, one line per binder, is the premise ledger
(`premises_output.txt`), which the continuous integration compares with the build's.  Each
hypothesis's line gives the definition it is and, after it, its full type, so the ledger shows the
instantiation of the definition (the field a premise speaks of, the acceleration a temperature is
taken at) and not its head alone.  An object whose type ends in `Prop`, a predicate or relation such
as `Closes` of `Main.deSitter_horizon`, is named "predicate object": it carries no content of its
own, and the premises that take it (`P1.slice_qubits` and `Geometry.space_form`, the second of
which fixes its meaning) say what it is, as their docstrings say.

So a premise can enter one of the paper's results in `Main.lean` only as a definition of
`Sources.lean`, where it stands next to the sentence of the paper it claims to be, and the account
of the premises is complete by construction.

The command makes four more checks, on the results taken together.

* **Every result takes something from a source.**  A result must take a premise of Postulate 1 or
  2, of thermodynamics, of quantum mechanics or of the cited geometry (the namespaces of
  `sourceNamespaces`), or a derived statement (namespace `Derived`), or an object of a structure
  that carries clauses of the postulates: an object whose type is one of `carriers`, or a family
  of such objects.  The one other kind of result takes nothing and states that such a structure
  has an instance, as `Main.register_in_band` states that a register exists.  A result that takes
  nothing from a source and states no such instance fails the build.  The block of each result
  ends with a line `rests on:` that names what was found.
* **Every derived statement is concluded.**  Each definition of the namespace `Derived` must be a
  conjunct of the conclusion of a result that takes something from a source and whose own derived
  premises are concluded before it, so that no derived statement rests on itself; or it must be,
  by its definition, such a statement at every time (`∀ s : ℝ, d …`, with `d` a derived statement
  that is concluded).  The ledger ends with one line for each derived statement, which names the
  result that concludes it.  A derived statement is matched by its name: the ledger shows the
  arguments at which a result takes it, and the statement of the result that concludes it shows
  those at which it is concluded.
* **Every theorem of the results' namespace is listed.**  Each theorem of the namespace
  `resultsNamespace`, or of a namespace under it, that stands before the command in its file must
  be among the theorems that the command is given.  The command stands at the end of `Main.lean`,
  so no theorem of that file's namespace stays outside the ledger.  The check reads the theorems,
  as Lean declares them, so a proof declared with `def` or `instance` is not read.  It passes
  over the names that Lean treats as internal details (`isInternalDetail`): a name with a part
  that begins with an underscore, with a numeric part, or with a last part "eq_", "match_",
  "proof_" or "omega_" followed only by digits and underscores, or by nothing.  Lean generates
  such names for a declaration, and a theorem that an author gave one would not be read either.
  Some names that Lean generates, such as "eq_def" for a definition, are not internal details
  and would be read; no definition, structure or inductive type stands in the results' namespace.
* **No result names a measured number.**  The check reads the statement of a result and the
  definition of every constant of the package that the statement names, and so on through every
  definition; of a theorem that a statement names it reads the statement and not the proof.  In
  all that it reads there must be no constant of the namespace `numbersNamespace`, where the
  measured inputs and the numbers computed from them stand (`Numerics.lean`), no decimal number
  (`OfScientific.ofScientific`, by which Lean reads a decimal), and no whole number above
  `numeralBound`.  Of a structure of the package the check reads the fields.  The measured inputs
  of `Numerics.lean` are written as whole numbers and their ratios, such as `299792458` and
  `66743/10^15`, and the bound keeps a number so written out of a statement and of a premise.
  The whole numbers that the results name are small, the `2` of `2^N ≤ L` or the `21/20` of
  `Main.simple_interpolation`, and the last line of the ledger gives the largest.  A measured
  value written with whole numbers below the bound alone, as the measured `a₀` is, `12/10^11`,
  would pass, and the check does not exclude it: the ledger prints every premise in full.  The
  results that state an instance of a structure of the postulates are excepted:
  `Main.register_in_band`, the one such result, places a register in the measured band of `L`
  and names the band.

What the checks do not show.  They read the statements, that is, what a result takes.  Lean's
unused-variables linter reports a hypothesis that neither the statement nor the proof mentions,
and the workflow builds with `--wfail`, so that its warning fails the build.  Whether the
conclusion needs a premise depends on the statement, and no check of the build tests it: a result
may state, beside what its premises give, a step of mathematics that needs none of them.  And a
derived statement taken at every time supposes the premises of its derivation at every time,
which is not checked.
-/

open Lean Elab Command Meta

namespace Register.Premises

/-- the heads of the types that an object may have, each the type of an object of some result of
`Main.lean`: numbers and indices (`Real`, `Nat`, `Bool`, `Fin`, with `Subtype` and `Membership.mem`
for the cells of a ring); the register and its structures (`Horizon`, its `Cell` and `Loop`,
`Horizon.Positions`, `Register.Reg`); the qubit and its tick (`Qubit.Op`, `Qubit.Tick`) and the
factor of a tick, a complex number (`Complex`, of which `En` gives the energy,
`Qubit.Tick.energy`), with the states of a qubit (`Qubit.Vec`), off which a law reads
(`Main.free_tick_hidden`); the space forms (`Space.SpaceForm`); a spacetime as the files see it
(`Einstein.Spacetime`, its points `Pt`); a curve of a spacetime (`Geodesic.Curve`); positions in
the plane of an orbit (`Prod`); the drawing of the rings as great circles of the three-sphere
(`Crossing.Drawing`), the quaternions of its rotations (`Quaternion`) and their weighting
(`MeasureTheory.Measure`); the words and codes of `Coding.lean` (`Coding.Word`, `Coding.LineCode`,
with a code as a subgroup of the words, `AddSubgroup`, and residues, `ZMod`); and finite sets and
types (`Finset`, `Fintype`, `DecidableEq`).  The list holds no type that no result takes: without
any one of them the build fails. -/
def allowedObjects : List Name :=
  [`Real, ``Nat, ``Bool, ``Fin, ``Subtype, ``Membership.mem,
   `Horizon, `Horizon.Cell, `Horizon.Loop, `Horizon.Positions,
   `Register.Reg, `Register.Qubit.Tick, `Register.Qubit.Op, `Register.Qubit.Vec, `Complex,
   `Space.SpaceForm, `Register.Einstein.Spacetime, `Register.Einstein.Spacetime.Pt,
   `Finset, ``Prod, `Crossing.Drawing, `MeasureTheory.Measure, `Geodesic.Curve, `Quaternion,
   `AddSubgroup, `ZMod, `Register.Coding.Word, `Register.Coding.LineCode,
   `Fintype, `DecidableEq]

/-- the namespace of the sources; a proposition with a head constant under it is a listed premise -/
def sourcesNamespace : Name := `Register.Sources

/-- the namespaces of the sources from which the files take premises: the two postulates (with
Sec. II's definitions), thermodynamics, quantum mechanics and the cited geometry.  A premise of
one of them is a premise from a source; a condition, the step at leading order and the choice of
units are not.  Quantum mechanics, which the paper's Sec. III lists for the gates of Sec. IV.A,
has the one premise `QM.gates`, which `Main.return_bound` takes. -/
def sourceNamespaces : List Name :=
  [`Register.Sources.P1, `Register.Sources.P2, `Register.Sources.Thermo, `Register.Sources.QM,
   `Register.Sources.Geometry]

/-- the namespace of the measured inputs and of the numbers computed from them (`Numerics.lean`);
no result may name a constant of it, but for a result that states an instance of a structure of
the postulates -/
def numbersNamespace : Name := `Register.Numerics

/-- the largest whole number that a result may name, in its statement or in a definition under
it, unless it states an instance of a structure of the postulates -/
def numeralBound : Nat := 100

/-- the namespace of the statements that `Main.lean` derives and other results take by name -/
def derivedNamespace : Name := `Register.Sources.Derived

/-- the structures whose fields carry clauses of the postulates, which the header of `Sources.lean`
lists: the register with Postulate 2's clauses on incidence (`Horizon`), its positions and its
maps (`Horizon.Positions`, `Horizon.Symmetry`), a qubit's states and ticks (`Qubit.Vec`,
`Qubit.Op`) and the free tick (`Qubit.Tick`).  A result that takes an object of one of them, or a
family of such objects, takes the clauses it carries. -/
def carriers : List Name :=
  [`Horizon, `Horizon.Positions, `Horizon.Symmetry, `Register.Qubit.Vec, `Register.Qubit.Op,
   `Register.Qubit.Tick]

/-- the namespace of the results: every theorem of it, or of a namespace under it, that stands
before `#premises` in its file must be among the theorems that the command is given -/
def resultsNamespace : Name := `Register.Main

/-- the classes a hypothesis may be: `NeZero L`, that `L` is not zero, and `Nonempty Ω`, that a
set of configurations is not empty -/
def allowedClasses : List Name := [``NeZero, ``Nonempty]

/-- the head constants of a type: of the type itself, of the domains of its function types, and of
the predicate of a subtype -/
partial def heads (e : Expr) : MetaM (Array Name) := do
  let e := (← instantiateMVars e).headBeta
  match e with
  | .forallE _ d b _ =>
    let hd ← heads d
    let hb ← withLocalDeclD `x d fun x => heads (b.instantiate1 x)
    return hd ++ hb
  | .sort _ => return #[]
  | .fvar _ => return #[]
  | .mvar _ => return #[]
  | .proj S _ _ => return #[S]
  | _ =>
    let fn := e.getAppFn
    match fn with
    | .const c _ =>
      if c == ``Subtype then
        match e.getAppArgs with
        | #[_, p] =>
          let hp ← match p with
            | .lam _ d b _ => withLocalDeclD `x d fun x => heads (b.instantiate1 x)
            | _ => heads p
          return #[c] ++ hp
        | _ => return #[c]
      else
        return #[c]
    | _ => return #[]

/-- whether a name lies in a namespace -/
def inNamespace (ns n : Name) : Bool := ns.isPrefixOf n

/-- the derived statements that a conclusion states: the conjuncts of the conclusion, under its
existential quantifiers, whose head is a definition of the namespace `Derived` (the first argument
bounds the depth of the search) -/
def concluded : Nat → Expr → MetaM (Array Name)
  | 0, _ => pure #[]
  | fuel + 1, e => do
    let e := (← instantiateMVars e).headBeta
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``And && args.size == 2 then
      return (← concluded fuel args[0]!) ++ (← concluded fuel args[1]!)
    else if fn.isConstOf ``Exists && args.size == 2 then
      lambdaTelescope args[1]! fun _ b => concluded fuel b
    else
      match fn with
      | .const c _ => return if inNamespace derivedNamespace c then #[c] else #[]
      | _ => return #[]

/-- the structures of `carriers` of which a conclusion states that an instance exists: the types
of the variables that the conjuncts of the conclusion bind with an existential quantifier (the
first argument bounds the depth of the search) -/
def instanced : Nat → Expr → MetaM (Array Name)
  | 0, _ => pure #[]
  | fuel + 1, e => do
    let e := (← instantiateMVars e).headBeta
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``And && args.size == 2 then
      return (← instanced fuel args[0]!) ++ (← instanced fuel args[1]!)
    else if fn.isConstOf ``Exists && args.size == 2 then
      let here : Array Name := match args[0]!.getAppFn with
        | .const c _ => if carriers.contains c then #[c] else #[]
        | _ => #[]
      return here ++ (← lambdaTelescope args[1]! fun _ b => instanced fuel b)
    else
      return #[]

/-- the derived statement that `d` is at every time, if the definition of `d` is `∀ s : ℝ, c …`
with `c` another definition of the namespace `Derived` -/
def everyTime (d : Name) : MetaM (Option Name) := do
  let some ci := (← getEnv).find? d | return none
  let some v := ci.value? | return none
  lambdaTelescope v fun _ body =>
    forallTelescope body fun xs b => do
      if xs.size != 1 then return none
      unless (← inferType xs[0]!).isConstOf `Real do return none
      match b.getAppFn with
      | .const c _ => return if c != d && inNamespace derivedNamespace c then some c else none
      | _ => return none

/-- what the check of one result found: the lines of its block of the ledger; the premises from a
source and the derived statements among its hypotheses; the structures of `carriers` of which it
takes an object, one or a family of them; the structures of which its conclusion states that an
instance exists; the derived statements that its conclusion states; and the numbers that it
names (`numbersNamed`): the constants of `numbersNamespace` and the reading of a decimal, and
the largest whole number, with the declaration that holds it -/
structure Taken where
  lines : Array String
  sources : Array Name
  derived : Array Name
  structures : Array Name
  instances : Array Name
  concludes : Array Name
  numbers : Array Name
  numeral : Nat
  numeralAt : Name

/-- a definition of `Sources.lean` without the namespace `Register.Sources` -/
def short (c : Name) : String := (c.replacePrefix sourcesNamespace Name.anonymous).toString

/-- a structure without the namespace `Register` -/
def shortStructure (c : Name) : String := (c.replacePrefix `Register Name.anonymous).toString

/-- the names of a list, separated by commas, or `none` -/
def listed (cs : Array String) : String :=
  if cs.isEmpty then "none" else String.intercalate ", " cs.toList

/-- the numbers that a result names: the constants of `numbersNamespace` and the reading of a
decimal, and the largest whole number with the declaration that holds it.  They are read off the
statement of the result and off the definition of every constant of the package that the
statement names, through every definition; of a theorem or an axiom only the statement is read,
and of a structure or another inductive type its constructors, which hold the fields.  The first
argument bounds the number of expressions read. -/
def numbersNamed (fuel : Nat) (n : Name) : CoreM (Array Name × Nat × Name) := do
  let env ← getEnv
  let info ← getConstInfo n
  let mut seen : NameSet := {}
  let mut bad : Array Name := #[]
  let mut big : Nat := 0
  let mut bigAt : Name := n
  let mut todo : Array (Name × Expr) := #[(n, info.type)]
  for _ in [0:fuel] do
    let some (owner, e) := todo.back? | break
    todo := todo.pop
    let ref ← IO.mkRef (0 : Nat)
    e.forEach' fun s => do
      if let .lit (.natVal k) := s then ref.modify (max k)
      return true
    let k ← ref.get
    if k > big then
      big := k
      bigAt := owner
    for c in e.getUsedConstants do
      unless seen.contains c do
        seen := seen.insert c
        if inNamespace numbersNamespace c || c == ``OfScientific.ofScientific then
          bad := bad.push c
        let inPackage := match env.getModuleIdxFor? c with
          | none => true
          | some idx => (`RegisterGravity).isPrefixOf env.header.moduleNames[idx.toNat]!
        if inPackage then
          match env.find? c with
          | some (.defnInfo d) => todo := (todo.push (c, d.type)).push (c, d.value)
          | some (.inductInfo i) =>
            todo := todo.push (c, i.type)
            for ctor in i.ctors do
              if let some ci := env.find? ctor then
                todo := todo.push (ctor, ci.type)
          | some ci => todo := todo.push (c, ci.type)
          | none => pure ()
  unless todo.isEmpty do
    throwError "the check of the numbers that `{n}` names did not end within its bound"
  return (bad, big, bigAt)

/-- check one theorem: list its binders, fail on any that is not a listed premise or object, and
collect what the theorem takes from the sources and what it concludes -/
def checkTheorem (n : Name) : TermElabM Taken := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs body => do
    let mut lines : Array String := #[s!"{n}"]
    let mut sources : Array Name := #[]
    let mut derived : Array Name := #[]
    let mut structures : Array Name := #[]
    for x in xs do
      let ty ← instantiateMVars (← inferType x)
      let name₀ ← x.fvarId!.getUserName
      let tyStr ← ppExpr ty
      let tyLine := (tyStr.pretty 1000).replace "\n" " "
      let name := if name₀.hasMacroScopes then s!"[{tyStr}]" else s!"{name₀}"
      if ← isProp ty then
        let fn := ty.headBeta.getAppFn
        match fn with
        | .const c _ =>
          if inNamespace sourcesNamespace c then
            let tag :=
              if inNamespace (sourcesNamespace ++ `Open) c then "  (OPEN)"
              else if inNamespace (sourcesNamespace ++ `Units) c then "  (units)"
              else if inNamespace (sourcesNamespace ++ `Approx) c then "  (leading order)"
              else if inNamespace (sourcesNamespace ++ `Derived) c then "  (derived in Main.lean)"
              else if inNamespace (sourcesNamespace ++ `Condition) c then "  (condition)"
              else ""
            if sourceNamespaces.any (fun ns => inNamespace ns c) && !sources.contains c then
              sources := sources.push c
            if inNamespace derivedNamespace c && !derived.contains c then
              derived := derived.push c
            lines := lines.push s!"  {name} : {c}{tag} = {tyLine}"
          else if allowedClasses.contains c then
            lines := lines.push s!"  {name} : {c} (class)"
          else
            throwError "premise `{name}` of `{n}` has the type `{ty}`, whose head `{c}` is not a definition of Sources.lean"
        | _ => throwError "premise `{name}` of `{n}` has the type `{ty}`, which is not a definition of Sources.lean"
      else
        let hs ← heads ty
        for h in hs do
          if !allowedObjects.contains h then
            throwError "object `{name}` of `{n}` has the type `{ty}`, whose head `{h}` is not an allowed object type"
        let kind := if ty.getForallBody.isProp then "predicate object" else "object"
        lines := lines.push s!"  {name} : {kind}, {tyLine}"
        -- an object of a structure that carries clauses of the postulates, or a family of them
        match ty.getForallBody.getAppFn with
        | .const c _ =>
          if carriers.contains c && !structures.contains c then structures := structures.push c
        | _ => pure ()
    structures := (carriers.filter fun c => structures.contains c).toArray
    let concludes ← concluded 64 body
    let instances ← instanced 64 body
    let tail := if instances.isEmpty then ""
      else s!"; states an instance of {listed (instances.map shortStructure)}"
    lines := lines.push s!"  rests on: sources {listed (sources.map short)}; derived {listed (derived.map short)}; structures {listed (structures.map shortStructure)}{tail}"
    let (numbers, numeral, numeralAt) ← numbersNamed 1000000 n
    return { lines, sources, derived, structures, instances, concludes, numbers, numeral, numeralAt }

/-- `#premises thm₁ thm₂ …`: the premise ledger of the named theorems -/
elab "#premises " ids:ident+ : command => do
  let mut taken : Array (Name × Taken) := #[]
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let t ← liftTermElabM <| checkTheorem n
    taken := taken.push (n, t)
  let env ← getEnv
  for c in carriers do
    unless env.contains c do
      throwError "the carrier `{c}` of Premises.lean is not a declaration"
  -- a result that takes nothing from a source and states no instance of a structure
  for (n, t) in taken do
    if t.sources.isEmpty && t.derived.isEmpty && t.structures.isEmpty && t.instances.isEmpty then
      throwError "the result `{n}` takes nothing from a source: none of its hypotheses is a premise of Postulate 1 or 2, of thermodynamics, of quantum mechanics or of the cited geometry, or a derived statement, none of its hypotheses and objects is of a structure that carries clauses of the postulates, and its conclusion states no instance of such a structure"
  -- a result that names a measured number and states no instance of a structure
  let mut named : Array String := #[]
  let mut largest : Nat := 0
  let mut largestAt : String := "none"
  for (n, t) in taken do
    if t.instances.isEmpty then
      unless t.numbers.isEmpty do
        throwError "the result `{n}` names a measured number, `{t.numbers[0]!}`, in its statement or in a definition under it: a constant of Numerics.lean or a decimal; a result takes no number"
      if t.numeral > numeralBound then
        throwError "the result `{n}` names the whole number {t.numeral}, above {numeralBound}, in `{t.numeralAt}`: its statement or a definition under it; a result takes no measured number"
      if t.numeral > largest then
        largest := t.numeral
        largestAt := s!"{n}"
    else
      named := named.push s!"{n}"
  -- the derived statements: the definitions of the namespace `Derived`; and the theorems of the
  -- results' namespace that stand before the command in its file, each of which must be listed
  let mut derivedAll : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.getPrefix == derivedNamespace && !n.isInternal then
      match ci with
      | .defnInfo _ => derivedAll := derivedAll.push n
      | _ => pure ()
    -- a private theorem counts by the name it was written with; a theorem of a namespace under
    -- the results' namespace counts too; a name that Lean treats as an internal detail, as those
    -- it generates for a declaration, does not (the header says which names these are)
    let user := privateToUserName n
    if resultsNamespace.isPrefixOf user && user != resultsNamespace && !user.isInternalDetail
        && (env.getModuleIdxFor? n).isNone then
      match ci with
      | .thmInfo _ =>
        unless taken.any (fun p => p.1 == n) do
          throwError "the theorem `{user}` stands in the file of the results and is not among those that `#premises` is given"
      | _ => pure ()
  derivedAll := derivedAll.qsort fun a b => a.toString < b.toString
  -- a derived statement that is another one at every time
  let mut atEveryTime : Array (Name × Name) := #[]
  for d in derivedAll do
    if let some c ← liftTermElabM <| everyTime d then
      atEveryTime := atEveryTime.push (d, c)
  -- the derived statements that are concluded, in the order in which they are: each by a result
  -- that takes something from a source and whose own derived premises were concluded before
  let mut done : Array (Name × String) := #[]
  for _ in [0:derivedAll.size + 1] do
    for d in derivedAll do
      unless done.any (fun p => p.1 == d) do
        match taken.find? (fun p => p.2.concludes.contains d
            && p.2.derived.all (fun d' => done.any (fun q => q.1 == d'))
            && !(p.2.sources.isEmpty && p.2.derived.isEmpty && p.2.structures.isEmpty)) with
        | some p => done := done.push (d, s!"concluded by {p.1}")
        | none =>
          match atEveryTime.find? (fun p => p.1 == d) with
          | some p =>
            if done.any (fun q => q.1 == p.2) then
              done := done.push (d, s!"{short p.2} at every time")
          | none => pure ()
  for d in derivedAll do
    unless done.any (fun p => p.1 == d) do
      throwError "the derived statement `{d}` is concluded by no result that takes something from a source and whose own derived premises are concluded without it, and is no such statement at every time"
  let mut all : Array String := #[]
  for (_, t) in taken do
    all := all ++ t.lines
  for d in derivedAll do
    match done.find? (fun p => p.1 == d) with
    | some p => all := all.push s!"derived {short d} : {p.2}"
    | none => pure ()
  all := all.push s!"{ids.size} results checked, every theorem of {resultsNamespace} before this command: every hypothesis is a definition of Sources.lean, NeZero or Nonempty, every object of an allowed type; every result takes something from a source or states an instance of a structure of the postulates; each of the {derivedAll.size} derived statements is concluded by a result or is such a statement at every time; no result names a constant of Numerics.lean, a decimal or a whole number above {numeralBound}, in its statement or in a definition under it, but for those that state an instance: {listed named}; the largest whole number that the others name is {largest}, in {largestAt}"
  logInfo m!"{String.intercalate "\n" all.toList}"

end Register.Premises
