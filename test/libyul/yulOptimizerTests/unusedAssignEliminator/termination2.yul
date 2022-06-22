{
    let r
    r := 1
    function f(x, y) {
        // Can be removed, is param
        x := 1
        y := 2
        if x {
            y := 2
            leave
        }
        // This enforces that some of the assignments above can be removed.
        mstore(0, x)
    }
    r := 2
}
// ----
// step: unusedAssignEliminator
//
// {
//     let r
//     function f(x, y)
//     {
//         x := 1
//         if x { leave }
//         mstore(0, x)
//     }
// }
