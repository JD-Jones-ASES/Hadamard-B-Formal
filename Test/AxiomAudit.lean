import Solution
import Lean

set_option linter.style.header false

/-!
# Public theorem axiom audit

The audit follows every public Palomar theorem transitively and fails
elaboration if a proof depends on anything beyond Lean's standard logical
axioms. In particular, this catches placeholders, custom axioms, and native
evaluation shortcuts in the solution proof closure.
-/

namespace HadamardBFormalAxiomAudit

open Lean Meta

def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

def auditedDeclarations : List Name :=
  [``HadamardBFormal.theoremA,
    ``HadamardBFormal.theoremA_sufficiency,
    ``HadamardBFormal.theoremB_profile,
    ``HadamardBFormal.D5,
    ``HadamardBFormal.D6,
    ``HadamardBFormal.goethalsSeidel_abelian,
    ``HadamardBFormal.borderedGS_index_one,
    ``HadamardBFormal.lemmaT,
    ``HadamardBFormal.twist_profile_iff,
    ``HadamardBFormal.twist_isConjugation,
    ``HadamardBFormal.twist_isHadamard_iff,
    ``HadamardBFormal.theoremD_tables,
    ``HadamardBFormal.theoremD_rowTable,
    ``HadamardBFormal.theoremD_border,
    ``HadamardBFormal.deltaSqSum_eq_four,
    ``HadamardBFormal.theoremD_transport,
    ``HadamardBFormal.collapse_seedProblem_bijection,
    ``HadamardBFormal.hadamard_52_bordered,
    ``HadamardBFormal.hadamardExists_52,
    ``HadamardBFormal.hadamard_20_bordered,
    ``HadamardBFormal.hadamardExists_20,
    ``HadamardBFormal.gate52_columnTable]

def runAxiomAudit : MetaM Unit := do
  let mut offenders : Array String := #[]
  for decl in auditedDeclarations do
    unless (← getEnv).contains decl do
      throwError "axiom audit: audited declaration `{decl}` does not exist"
    let axioms ← Lean.collectAxioms decl
    logInfo s!"axioms {decl}: {axioms.toList}"
    let bad := axioms.filter fun axiomName ↦ !allowedAxioms.contains axiomName
    unless bad.isEmpty do
      offenders := offenders.push s!"{decl} depends on {bad.toList}"
  unless offenders.isEmpty do
    throwError "axiom audit FAILED: {String.intercalate "; " offenders.toList}"
  logInfo s!"axiom audit passed: {auditedDeclarations.length} declarations; \
    axioms confined to {allowedAxioms}"

#eval runAxiomAudit

end HadamardBFormalAxiomAudit
