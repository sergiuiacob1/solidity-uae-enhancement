{
    let x, y, z := foo(sload(0),sload(32))
    sstore(0, x)
    sstore(0, y)
    sstore(0, z)
    x, y, z := foo(sload(32), sload(8))

    // out3 is unassigned.
    function foo(a, b) -> out1, out2, out3
    {
        out1 := mload(32)
        out1 := sload(out1)
        out2 := add(out1, 1)
        extcodecopy(out1, out1, 1, b)
        // to prevent foo from getting inlined
        if iszero(out1) { leave }
    }
}
// ----
// step: fullSuite
//
// { { sstore(0, 0) } }
