import DirectedFlowCutGap.EncodedShortcutReachability

open DirectedFlowCutGap.EncodedShortcutReachability

def shortcutChain : Input 4 :=
  { adjacency := Vector.ofFn fun u => Vector.ofFn fun v =>
      decide ((u.val=0 ∧ v.val=1) ∨ (u.val=1 ∧ v.val=2) ∨
        (u.val=2 ∧ v.val=3) ∨ (u.val=2 ∧ v.val=1) ∨ (u.val=0 ∧ v.val=0))
    removed := #v[false,true,true,false] }

def shortcutBlocked : Input 4 := { shortcutChain with removed := #v[false,true,false,false] }
def shortcutEmpty : Input 0 := ⟨#v[],#v[]⟩

#eval do
  let a := shortcutChain.materialize
  unless a.adjacency[0][3] do throw (IO.userError "removed-interior chain was missed")
  unless !(a.adjacency[3][0]) do throw (IO.userError "unreachable reverse edge was added")
  unless !(a.adjacency[0][0]) do throw (IO.userError "zero-length/self-loop shortcut was added")
  let b := shortcutBlocked.materialize
  unless !(b.adjacency[0][3]) do throw (IO.userError "surviving interior was incorrectly bypassed")
  unless shortcutEmpty.materialize.adjacency.toArray.isEmpty do
    throw (IO.userError "empty matrix was not preserved")
  IO.println "PASS: removed interiors, surviving-interior obstruction, cycles, self-loop exclusion, unreachable and empty graphs"
