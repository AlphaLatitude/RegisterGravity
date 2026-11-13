import RegisterGravity
/-! # Which declarations does a result, a certified number, a model or a statement of the paper reach?

The README says that every name of the ledger is reached by a result of `Main.lean`, a certified
number or a model, or is a statement of the paper proved where it stands.  This script
follows, from four sets of roots, the constants that each declaration's type and value use, within
the package:
* `MAIN`: the theorems of `Main.lean`;
* `NUM`: the theorems of `Numerics.lean`, the certified numbers;
* `MODEL`: the declarations of `Models.lean`, every declaration whose name ends in `model`,
  `Reg.hypotheses_consistent`, and `Qubit.Tick.ofPhase`, the tick of any phase;
* `PAPER`: the statements of the paper that are proved where they stand and not restated in
  `Main.lean`, named below with the place where the paper states each.
It prints every name of `Ledger.lean` with the first set that reaches it, `MAIN`, `NUM`, `MODEL`,
`PAPER` or `NONE`, and every other declaration of the package that none reaches, the constants
that Lean generates included.  A line `LEDGER NONE` or `REACH MISSING-ROOT` is a failure: the
continuous integration runs the script and fails on either.  Run from the package directory, after
`lake build`: `lake env lean scripts/Reach.lean`. -/
open Lean Elab Command

/-- the statements of the paper proved where they stand -/
def paperRoots : Array Name := #[
  -- Sec. IV.A, the linear cluster state with one layer of generic rotations
  `Register.Cluster.chain_card, `Register.Cluster.step_card, `Register.Cluster.step_ne_zero,
  `Register.Cluster.moebius_injOn, `Register.Cluster.moebius_collision,
  `Register.Cluster.moebius_ne_zero, `Register.Cluster.ratio_eq_neg_normSq,
  -- Secs. II and IV.E, the free tick is one factor, a phase, on every state of the string
  `Register.Qubit.Tick.phase_unique, `Register.Qubit.Tick.norm_scalar,
  -- Secs. II and IV.E, the factor of the tick on the string of each sense
  `Register.Qubit.Tick.mulVec_e₁, `Register.Qubit.Tick.mulVec_e₂,
  -- Sec. IV.E, the mean energy in equal steps and the global phase's mean decrease, a radian a lap
  `Register.Law.gibbsLadder_eq, `Register.Law.gibbsLadder_within_step, `Register.Reg.string_tick,
  -- Sec. IV.C, the carriers' share in finite form, and Eq. (law)
  `Register.Law.share_of_equipartition, `Register.Reg.law,
  -- Sec. IV.A, which states a pairing shows exactly, most product states not among them, the
  -- pairing not fixed by the strings, the probability of a joint outcome as the product of the
  -- frequencies on its blocks, what a block resolves, the state from the strings and their
  -- blocks' phases, and what a sample sees
  `Register.Pairing.shown_exactly_iff, `Register.Pairing.most_products_not_shown,
  `Register.Pairing.pairing_not_fixed, `Register.Pairing.freq_chain,
  `Register.Pairing.block_resolution,
  `Register.Pairing.state_of_strings, `Register.Pairing.sample_outcomes_le,
  -- Sec. IV.A, the conditional states of a product state, of a cluster state, of a stabilizer
  -- measurement, and of a state that depends on the earlier qubits through a count, and a
  -- string with room for them
  `Register.Conditional.card_product_states_le_one, `Register.Conditional.clusterSign_eq,
  `Register.Conditional.factor_depends, `Register.Conditional.card_cluster_states_le_two,
  `Register.Conditional.stabilizer_bit, `Register.Conditional.card_stab_states_le_two,
  `Register.Conditional.card_states_by_count, `Register.Conditional.two_cells_fit,
  `Register.Conditional.room_holds, `Register.Conditional.stabilizer_held,
  `Register.Conditional.product_one_state,
  -- Sec. II, the strings not yet scattered, and the two radii near the observer
  `Register.Strings.unscattered, `Register.Reg.radii_agree,
  -- Sec. IV.B, an accelerated observer's own horizon
  `Register.Reg.La_lt_L,
  -- Sec. IV.C, the two points where a ring crosses a sphere, its two receiving cells, and the
  -- bit that unequal energies of the two senses would take
  `Crossing.two_crossings, `Register.Qubit.entropy_lt_of_energies_ne,
  -- Secs. III and IV.D, the limit up to which the solution with a mass has a horizon
  `Register.Reg.horizon_limit,
  -- Secs. IV.C and IV.E, the matter a string holds on average, and the split of a string's energy,
  -- which is not string by string
  `Register.Reg.matter_eq, `Register.Reg.split_not_stringwise]

def reachClosure (env : Environment) (inPkg : Name → Bool) (roots : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    for m in ci.getUsedConstantsAsSet.toList do
      if inPkg m && !seen.contains m then stack := stack.push m
  return seen

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => Name.anonymous
  let inPkg (n : Name) : Bool := (`RegisterGravity).isPrefixOf (modOf n)
  for n in paperRoots do
    unless env.contains n do logInfo m!"REACH MISSING-ROOT {n}"
  let mut main : Array Name := #[]
  let mut num : Array Name := #[]
  let mut model : Array Name := #[`Register.Qubit.Tick.ofPhase]
  let mut all : Array Name := #[]
  for (n, ci) in env.constants.toList do
    unless inPkg n do continue
    if n.isInternal then continue
    all := all.push n
    let isThm := match ci with | .thmInfo _ => true | _ => false
    let last := n.getString!
    if modOf n == `RegisterGravity.Main && isThm && (`Register.Main).isPrefixOf n then main := main.push n
    if modOf n == `RegisterGravity.Numerics && isThm then num := num.push n
    if modOf n == `RegisterGravity.Models || last.endsWith "model" || last == "hypotheses_consistent" then
      model := model.push n
  let sMain := reachClosure env inPkg main
  let sNum := reachClosure env inPkg num
  let sModel := reachClosure env inPkg model
  let sPaper := reachClosure env inPkg paperRoots
  logInfo m!"REACH roots: MAIN {main.size}, NUM {num.size}, MODEL {model.size}, PAPER {paperRoots.size}; declarations {all.size}"
  let src ← (IO.FS.readFile "RegisterGravity/Ledger.lean" : IO String)
  let mut ledger : Std.HashSet Name := {}
  let mut cnt : Std.HashMap String Nat := {}
  for line in src.splitOn "\n" do
    if line.startsWith "#print axioms " then
      let nm := (line.drop 14).trim.toName
      ledger := ledger.insert nm
      let tag := if sMain.contains nm then "MAIN" else if sNum.contains nm then "NUM"
        else if sModel.contains nm then "MODEL" else if sPaper.contains nm then "PAPER" else "NONE"
      cnt := cnt.insert tag (cnt.getD tag 0 + 1)
      logInfo m!"LEDGER {tag} {nm} ({modOf nm})"
  for (t, k) in cnt.toList do logInfo m!"REACH ledger {t} {k}"
  let mut nother : Nat := 0
  for n in all do
    if ledger.contains n then continue
    if sMain.contains n || sNum.contains n || sModel.contains n || sPaper.contains n then continue
    let ci := (env.find? n).get!
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
    nother := nother + 1
    logInfo m!"OTHER-UNREACHED {kind} {n} ({modOf n})"
  logInfo m!"REACH other declarations unreached {nother}"
