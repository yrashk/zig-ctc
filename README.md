# Compile-time Contracts for Zig

Compile-time contracts address the duck-typing problem in Zig. When you have
a function taking `type` or `anytype` parameters, it's not trivial to tell
what that type should be like.

One can write good documentation but that requires extra maintenance efforts
and is not very formalized.

There's `std.meta.trait` but it is limited in terms of what it can do, and particulary,
it's not great at identifying the cause of contract (trait) and have limited composition.

This library offers simple, composable contracts that can track causes of contract violation.

There are two primary ways contracts can be used. They can be used directly in function's body:

```zig
const contracts = @import("./src/lib.zig");

fn body_contract(t: anytype) void {
    comptime contracts.require(contracts.is(@TypeOf(t), u8));
}
```

or function's signature:

```zig
fn signature_contract(t: anytype) contracts.RequiresAndReturns(
    contracts.is(@TypeOf(t), u8),
    void,
) {}

pub fn main() void {
    body_contract(@as(u8, 1));
    signature_contract(@as(u8, 1));
}
```
