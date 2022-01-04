//! Compile-time Contracts
//!
//! Compile-time contracts address the duck-typing problem in Zig. When you have
//! a function taking `type` or `anytype` parameters, it's not trivial to tell
//! what that type should be like.
//!
//! One can write good documentation but that requires extra maintenance efforts
//! and is not very formalized.
//!
//! There's `std.meta.trait` but it is limited in terms of what it can do, and particulary,
//! it's not great at identifying the cause of contract (trait) and have limited composition.
//! 
//! This library offers simple, composable contracts that can track causes of contract violation.
//!
//! There are two primary ways contracts can be used. They can be used directly in function's body:
//!
//! ```
//! const contracts = @import("./src/lib.zig");
//! 
//! fn body_contract(t: anytype) void {
//!     comptime contracts.require(contracts.is(@TypeOf(t), u8));
//! }
//! ```
//! 
//! or function's signature:
//! 
//! ```
//! fn signature_contract(t: anytype) contracts.RequiresAndReturns(
//!     contracts.is(@TypeOf(t), u8),
//!     void,
//! ) {}
//! 
//! pub fn main() void {
//!     body_contract(@as(u8, 1));
//!     signature_contract(@as(u8, 1));
//! }
//! ```

const std = @import("std");

pub const OutcomeTag = enum {
    Valid,
    Invalid,
};

pub const Identifier = []const u8;

pub const Invalid = struct {
    identifier: Identifier,
    causes: []const Outcome = &[0]Outcome{},

    /// Returns the first outcome that causes this outcome's failure
    pub fn cause(comptime self: @This()) Outcome {
        if (self.causes.len > 0)
            return self.causes[0].Invalid.cause();
        return Outcome.init(false, Invalid{ .identifier = self.identifier });
    }
};

/// Outcome of a contract
pub const Outcome = union(OutcomeTag) {
    Valid: Identifier,
    Invalid: Invalid,

    pub fn init(validity: bool, invalid: Invalid) @This() {
        return if (validity) .{ .Valid = invalid.identifier } else .{ .Invalid = invalid };
    }

    /// Returns the identifier of a contract
    pub fn identifier(comptime self: @This()) Identifier {
        return switch (self) {
            .Valid => |i| i,
            .Invalid => |inv| inv.identifier,
        };
    }

    fn collectFailures(comptime t1: @This(), comptime t2: @This()) []const @This() {
        comptime {
            var n: usize = 0;
            if (t1 == .Invalid) n += 1;
            if (t2 == .Invalid) n += 1;

            var causes: [n]@This() = [_]@This(){undefined} ** n;

            var i: usize = 0;
            if (t1 == .Invalid) {
                causes[i] = t1;
                i += 1;
            }
            if (t2 == .Invalid) {
                causes[i] = t2;
            }
            return &causes;
        }
    }

    /// Create a new Outcome that is requires both `self` and `t` to be valid
    pub fn andAlso(comptime self: @This(), comptime t: @This()) @This() {
        return @This().init(self == .Valid and t == .Valid, Invalid{
            .identifier = std.fmt.comptimePrint("{s}.andAlso({s})", .{ self.identifier(), t.identifier() }),
            .causes = @This().collectFailures(self, t),
        });
    }

    /// Create a new Outcome that is requires either `self` or `t` to be valid
    pub fn orElse(comptime self: @This(), comptime t: @This()) @This() {
        return @This().init(self == .Valid or t == .Valid, Invalid{
            .identifier = std.fmt.comptimePrint("{s}.orElse({s})", .{ self.identifier(), t.identifier() }),
            .causes = Outcome.collectFailures(t, self),
        });
    }
};

/// Creates a new Outcome that requires type `T` to be the same type as `T1`
pub fn is(comptime T: type, comptime T1: type) Outcome {
    return Outcome.init(T == T1, Invalid{
        .identifier = std.fmt.comptimePrint("is({}, {})", .{ T, T1 }),
    });
}

const expect = std.testing.expect;

test "is" {
    comptime {
        try expect(is(u8, u8) == .Valid);
        try expect(is(u8, u16) == .Invalid);
        try expect(std.mem.eql(u8, "is(u8, u16)", is(u8, u16).identifier()));
        try expect(is(u8, u16).Invalid.causes.len == 0);
    }
}

test "andAlso" {
    comptime {
        const T = u8;
        const valid_outcome = is(T, u8).andAlso(is(T, u8));
        try expect(valid_outcome == .Valid);

        const outcome = is(T, u8).andAlso(is(T, u16));
        try expect(outcome == .Invalid);

        try expect(std.mem.eql(u8, "is(u8, u8).andAlso(is(u8, u16))", outcome.identifier()));
        try expect(outcome.Invalid.causes.len == 1);

        try expect(std.mem.eql(u8, outcome.Invalid.causes[0].identifier(), is(T, u16).identifier()));
    }
}

test "orElse" {
    comptime {
        const T = u8;
        const valid_outcome = is(T, u8).orElse(is(T, u16));
        try expect(valid_outcome == .Valid);

        const outcome = is(T, u1).orElse(is(T, u17));
        try expect(outcome == .Invalid);

        try expect(std.mem.eql(u8, "is(u8, u1).orElse(is(u8, u17))", outcome.identifier()));
        try expect(outcome.Invalid.causes.len == 2);

        try expect(std.mem.eql(u8, outcome.Invalid.causes[0].identifier(), is(T, u17).identifier()));
        try expect(std.mem.eql(u8, outcome.Invalid.causes[1].identifier(), is(T, u1).identifier()));
    }
}

test "invalid outcome cause" {
    comptime {
        const T = u8;
        try expect(std.mem.eql(
            u8,
            is(T, u16).identifier(),
            is(T, u16).Invalid.cause().identifier(),
        ));

        const outcome = is(T, u8).andAlso(is(T, u16));
        try expect(outcome == .Invalid);
        try expect(std.mem.eql(
            u8,
            is(T, u16).identifier(),
            outcome.Invalid.cause().identifier(),
        ));

        const nested = (Outcome{ .Valid = "1" })
            .andAlso((Outcome{ .Valid = "2" }).andAlso(Outcome{ .Invalid = .{ .identifier = "3" } }));
        try expect(std.mem.eql(u8, "3", nested.Invalid.cause().identifier()));
    }
}

/// Requires an outcome to be valid, throws a compile-time error otherwise
pub fn require(comptime outcome: Outcome) void {
    if (outcome == .Invalid) {
        const err = std.fmt.comptimePrint(
            "requirement failure in {s}, cause: {s}",
            .{ outcome.identifier(), outcome.Invalid.cause().identifier() },
        );
        @compileError(err);
    }
}

/// Requires an outcome to be valid, throws a compile-time error otherwise
///
/// Used in function signatures:
///
/// ```
/// fn signature_contract(t: anytype) contracts.RequiresAndReturns(
///     contracts.is(@TypeOf(t), u8),
///     void,
/// ) {}
/// ```
pub fn RequiresAndReturns(outcome: Outcome, comptime T: type) type {
    require(outcome);
    return T;
}
