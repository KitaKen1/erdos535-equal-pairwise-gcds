import Comparator

open Lean

def main (args : List String) : IO Unit := do
  let [challengePath, candidatePath] := args
    | throw <| IO.userError "Expected the challenge and candidate exports."
  let challenge ← Export.parseStream (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk challengePath .read))
  let candidate ← Export.parseStream (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk candidatePath .read))
  let targets := #[`FCReference.erdos_535, `FCReference.erdos_535.variants.first_open_case,
    `FCReference.erdos_535.variants.sunflower_strong]
  let axioms := #[`propext, `Classical.choice, `Quot.sound]
  -- The targets are proposition definitions, so compare their bodies and dependencies.
  IO.ofExcept <| Comparator.compareAt challenge candidate axioms #[]
    (targets ++ #[`optParam, `autoParam, `semiOutParam, `outParam])
  for target in targets do
    IO.println s!"Comparator verified {target}"
