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
const expect = std.testing.expect;

pub const Identifier = []const u8;

pub const Valid = struct {
    identifier: Identifier,

    fn clone(self: @This()) @This() {
        return Invalid{
            .identifier = self.identifier,
        };
    }
};

pub const Invalid = struct {
    identifier: Identifier,

    /// outcomes that caused this outcome to be invalid
    /// (primarily concerns composite outcomes)
    causes: []const Outcome = &[0]Outcome{},

    /// reason for violation
    reason: []const u8 = "none given",

    /// Returns the first outcome that causes this outcome's failure
    pub fn cause(comptime self: @This()) Outcome {
        if (self.causes.len > 0)
            return self.causes[0].Invalid.cause();
        return Outcome.init(false, self.clone());
    }

    fn clone(self: @This()) @This() {
        return Invalid{
            .identifier = self.identifier,
            .reason = self.reason,
            .causes = self.causes,
        };
    }
};

/// Outcome of a contract
pub const Outcome = union(enum) {
    Valid: Valid,
    Invalid: Invalid,

    pub fn init(validity: bool, invalid: Invalid) @This() {
        return if (validity) .{
            .Valid = .{ .identifier = invalid.identifier },
        } else .{
            .Invalid = invalid,
        };
    }

    fn clone(comptime self: @This()) @This() {
        return Outcome.init(
            self == .Valid,
            (if (self == .Valid) Invalid{
                .identifier = self.identifier(),
            } else self.Invalid.clone()),
        );
    }

    /// Returns the identifier of a contract
    pub fn identifier(comptime self: @This()) Identifier {
        return switch (self) {
            .Valid => |v| v.identifier,
            .Invalid => |i| i.identifier,
        };
    }

    fn collectFailures(comptime t1: @This(), comptime t2: @This()) []const @This() {
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

    /// A contract that requires both `self` and `t` to be valid
    pub fn andAlso(comptime self: @This(), comptime t: @This()) @This() {
        return @This().init(self == .Valid and t == .Valid, Invalid{
            .identifier = std.fmt.comptimePrint("{s}.andAlso({s})", .{ self.identifier(), t.identifier() }),
            .causes = @This().collectFailures(self, t),
        });
    }

    fn isThenContract(comptime Then: type) @This() {
        // This contract does not use `andThen` to avoid infinite recursion
        const contract = isType(Then, .Struct)
            .andAlso(hasDecl(Then, "then"));
        return contract.named(std.fmt.comptimePrint(
            "isThenContract({s})",
            .{@typeName(Then)},
        ));
    }

    /// A contract that requires `self` to be valid and if it is, the
    /// contract returned by Then.then() has to be valid as well
    pub fn andThen(comptime self: @This(), comptime Then: type) @This() {
        require(isThenContract(Then));
        if (self == .Invalid)
            return self.clone();
        return Then.then().named(std.fmt.comptimePrint("andThen({s})", .{@typeName(Then)}));
    }

    /// A contract that requires `self` to be valid and if it is not, the
    /// contract returned by Then.then() has to be valid
    pub fn orThen(comptime self: @This(), comptime Then: type) @This() {
        //require(isThenContract(Then));
        if (self == .Valid)
            return self.clone();
        return Then.then().named(std.fmt.comptimePrint("orThen({s})", .{@typeName(Then)}));
    }

    /// A contract that requires either `self` or `t` to be valid
    pub fn orElse(comptime self: @This(), comptime t: @This()) @This() {
        return @This().init(self == .Valid or t == .Valid, Invalid{
            .identifier = std.fmt.comptimePrint("{s}.orElse({s})", .{ self.identifier(), t.identifier() }),
            .causes = Outcome.collectFailures(t, self),
        });
    }

    /// Gives an outcome a new identifier, wrapping the original outcome as a cause
    ///
    /// Useful for creating named contracts that compose other contracts together
    ///
    /// ```
    /// pub fn isMyThing(compile T: type) contracts.Outcome {
    ///     return contracts.isType(T, .Struct).named("isMyThing");
    /// }
    /// ```
    pub fn named(comptime self: @This(), identifier_: []const u8) @This() {
        return @This().init(self == .Valid, Invalid{ .identifier = identifier_, .causes = &[1]Outcome{self} });
    }
};

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

test "andThen" {
    comptime {
        var a = 1;
        const outcome = is(u8, u8).andThen(struct {
            pub fn then() Outcome {
                a = 2;
                return is(u8, u16);
            }
        });
        try expect(outcome == .Invalid);
        // andThen got to executed
        try expect(a == 2);

        const outcome1 = is(u8, u16).andThen(struct {
            pub fn then() Outcome {
                a = 3;
                return is(u8, u16);
            }
        });

        try expect(outcome1 == .Invalid);
        // andThen didn't get to execute
        try expect(a == 2);
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

test "orThen" {
    comptime {
        var a = 1;
        const outcome = is(u8, u8).orThen(struct {
            pub fn then() Outcome {
                a = 2;
                return is(u8, u16);
            }
        });
        try expect(outcome == .Valid);
        // orThen didn't get executed
        try expect(a == 1);

        const outcome1 = is(u8, u16).orThen(struct {
            pub fn then() Outcome {
                a = 2;
                return is(u8, u16);
            }
        });

        try expect(outcome1 == .Invalid);
        //// orThen got to execute
        try expect(a == 2);
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
        try expect(std.mem.eql(
            u8,
            outcome.Invalid.reason,
            outcome.Invalid.cause().Invalid.reason,
        ));

        const custom_reason = Outcome{ .Invalid = .{ .identifier = "custom", .reason = "custom" } };
        try expect(std.mem.eql(u8, custom_reason.Invalid.reason, custom_reason.Invalid.cause().Invalid.reason));

        const nested = (Outcome{ .Valid = .{ .identifier = "1" } })
            .andAlso(
            (Outcome{ .Valid = .{ .identifier = "2" } })
                .andAlso(Outcome{ .Invalid = .{ .identifier = "3", .reason = "special" } }),
        );
        try expect(std.mem.eql(u8, "3", nested.Invalid.cause().identifier()));
        try expect(std.mem.eql(u8, "special", nested.Invalid.cause().Invalid.reason));
    }
}

test "Outcome.named" {
    comptime {
        const outcome = is(u8, u16).named("contract");
        try expect(outcome == .Invalid);
        try expect(std.mem.eql(u8, "contract", outcome.identifier()));
        try expect(std.mem.eql(u8, "is(u8, u16)", outcome.Invalid.cause().identifier()));
    }
}

/// A contract that requires type `T` to be the same type as `T1`
pub fn is(comptime T: type, comptime T1: type) Outcome {
    return Outcome.init(T == T1, Invalid{
        .identifier = std.fmt.comptimePrint("is({}, {})", .{ T, T1 }),
    });
}

test "is" {
    comptime {
        try expect(is(u8, u8) == .Valid);
        try expect(is(u8, u16) == .Invalid);
        try expect(std.mem.eql(u8, "is(u8, u16)", is(u8, u16).identifier()));
        try expect(is(u8, u16).Invalid.causes.len == 0);
    }
}

/// A contract that requires that type `T` has to be of a certain
/// type (as in .Struct, .Int, etc.)
///
/// Includes violation reason into `Invalid.reason`
pub fn isType(comptime T: type, type_id: std.builtin.TypeId) Outcome {
    return Outcome.init(@typeInfo(T) == type_id, Invalid{
        .identifier = std.fmt.comptimePrint("isType({}, .{s})", .{ T, @tagName(type_id) }),
        .reason = std.fmt.comptimePrint("got .{s}", .{@tagName(@typeInfo(T))}),
    });
}

test "isType" {
    comptime {
        try expect(isType(struct {}, .Struct) == .Valid);
        try expect(isType(u8, .Struct) == .Invalid);
        try expect(std.mem.eql(u8, "got .Int", isType(u8, .Struct).Invalid.reason));
        try expect(std.mem.eql(u8, "isType(u8, .Struct)", isType(u8, .Struct).identifier()));
    }
}

pub fn hasDecl(comptime T: type, name: []const u8) Outcome {
    require(isType(T, .Struct).orElse(isType(T, .Enum).orElse(isType(T, .Union).orElse(isType(T, .Opaque)))));

    return Outcome.init(@hasDecl(T, name), Invalid{
        .identifier = std.fmt.comptimePrint("hasDecl({}, .{s})", .{ T, name }),
    });
}

test "hasDecl" {
    comptime {
        try expect(hasDecl(struct {}, "a") == .Invalid);
        try expect(hasDecl(struct {
            const a = 1;
        }, "a") == .Valid);
        try expect(hasDecl(enum {
            a,
        }, "a") == .Invalid);
        try expect(hasDecl(enum {
            a,
            const b = 1;
        }, "b") == .Valid);

        try expect(hasDecl(union(enum) {
            a: void,
        }, "a") == .Invalid);
        try expect(hasDecl(union(enum) {
            a: void,
            const b = 1;
        }, "b") == .Valid);
    }
}

/// Requires an outcome to be valid, throws a compile-time error otherwise
pub fn require(comptime outcome: Outcome) void {
    if (outcome == .Invalid) {
        const err = if (std.mem.eql(u8, outcome.identifier(), outcome.Invalid.cause().identifier()) and
            std.mem.eql(u8, outcome.Invalid.reason, outcome.Invalid.cause().Invalid.reason))
            std.fmt.comptimePrint(
                "requirement failure in {s} (reason: {s})",
                .{
                    outcome.identifier(),
                    outcome.Invalid.reason,
                },
            )
        else
            std.fmt.comptimePrint(
                "requirement failure in {s} (reason: {s}), cause: {s} (reason: {s})",
                .{
                    outcome.identifier(),
                    outcome.Invalid.reason,
                    outcome.Invalid.cause().identifier(),
                    outcome.Invalid.cause().Invalid.reason,
                },
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
