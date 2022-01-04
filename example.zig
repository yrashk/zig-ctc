const contracts = @import("./src/lib.zig");

fn body_contract(t: anytype) void {
    comptime contracts.require(contracts.is(@TypeOf(t), u8));
}

fn signature_contract(t: anytype) contracts.RequiresAndReturns(
    contracts.is(@TypeOf(t), u8),
    void,
) {}

pub fn main() void {
    body_contract(@as(u8, 1));
    signature_contract(@as(u8, 1));
}
