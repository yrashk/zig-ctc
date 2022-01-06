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

    /// A contract that requires `self` to be valid and if it is, the
    /// contract returned by Then.then() has to be valid as well
    pub fn andThen(comptime self: @This(), comptime Then: type) @This() {
        if (self == .Invalid)
            return self.clone();
        return Then.then().named(std.fmt.comptimePrint("andThen({s})", .{@typeName(Then)}));
    }

    /// A contract that requires `self` to be valid and if it is not, the
    /// contract returned by Then.then() has to be valid
    pub fn orThen(comptime self: @This(), comptime Then: type) @This() {
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

fn fnArgsEql(comptime a: []const std.builtin.TypeInfo.FnArg, comptime b: []const std.builtin.TypeInfo.FnArg) bool {
    if (a.len != b.len) return false;
    if (a.ptr == b.ptr) return true;
    for (a) |item, index| {
        if (b[index].is_generic != item.is_generic) return false;
        if (b[index].is_noalias != item.is_noalias) return false;
        if (b[index].arg_type == null and item.arg_type != null) return false;
        if (b[index].arg_type != null and item.arg_type != null and b[index].arg_type.? != item.arg_type.?) return false;
    }
    return true;
}

fn isGenericFnEqual(comptime T: type, comptime T1: type) bool {
    comptime {
        if (@typeInfo(T) != .Fn or @typeInfo(T) != .Fn)
            return false;
        const ti = @typeInfo(T).Fn;
        const ti1 = @typeInfo(T1).Fn;
        return ti.calling_convention == ti1.calling_convention and ti.alignment == ti1.alignment and
            ((ti.return_type == null and ti1.return_type == null) or (ti.return_type.? == ti1.return_type.?)) and
            fnArgsEql(ti.args, ti1.args);
    }
}

/// A contract that requires type `T` to be the same type as `T1`
pub fn is(comptime T: type, comptime T1: type) Outcome {
    const valid = if (isGenericFn(T) == .Valid and isGenericFn(T1) == .Valid) isGenericFnEqual(T, T1) else T == T1;
    return Outcome.init(valid, Invalid{
        .identifier = std.fmt.comptimePrint("is({}, {})", .{ T, T1 }),
    });
}

test "is" {
    comptime {
        try expect(is(u8, u8) == .Valid);
        try expect(is(u8, u16) == .Invalid);
        try expect(std.mem.eql(u8, "is(u8, u16)", is(u8, u16).identifier()));
        try expect(is(u8, u16).Invalid.causes.len == 0);
        try expect(is(fn (u8) u8, fn (u8) u8) == .Valid);
        try expect(is(fn (type) u8, fn (type) u8) == .Valid);
        // FIXME: figure out what to do with the return type, it's not really validating it
        // try expect(is(fn (type) u8, fn (type) bool) == .Invalid);
    }
}

/// A contract that requires function type T be generic
pub fn isGenericFn(comptime T: type) Outcome {
    comptime {
        const identifier = std.fmt.comptimePrint("isGenericFn({})", .{T});
        return isType(T, .Fn).andThen(struct {
            pub fn then() Outcome {
                return Outcome.init(@typeInfo(T).Fn.is_generic, Invalid{ .identifier = identifier });
            }
        }).named(identifier);
    }
}

test "isGenericFn" {
    comptime {
        try expect(isGenericFn(fn (type) bool) == .Valid);
        try expect(isGenericFn(fn (bool) bool) == .Invalid);
        try expect(isGenericFn(u8) == .Invalid);
    }
}

/// A contract that requires that type `T` has to be of a certain
/// type (as in .Struct, .Int, etc.)
///
/// Includes violation reason into `Invalid.reason`
pub fn isType(comptime T: type, comptime type_id: std.builtin.TypeId) Outcome {
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

/// A contract that requires that a given type is a struct,
/// enum, union or an opaque type that has a declaration by the given name.
pub fn hasDecl(comptime T: type, comptime name: []const u8) Outcome {
    const ti = @typeInfo(T);
    const validType = ti == .Struct or ti == .Enum or ti == .Union or ti == .Opaque;

    const valid = if (validType) @hasDecl(T, name) else false;
    const reason = if (validType) "declaration not found" else std.fmt.comptimePrint("{s} is not a struct, enum, union or an opaque type", .{T});

    return Outcome.init(valid, Invalid{
        .identifier = std.fmt.comptimePrint("hasDecl({}, {s})", .{ T, name }),
        .reason = reason,
    });
}

test "hasDecl" {
    comptime {
        try expect(hasDecl(u8, "a") == .Invalid);
        try expect(std.mem.eql(u8, hasDecl(u8, "a").Invalid.reason, "u8 is not a struct, enum, union or an opaque type"));
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

/// A contract that requires that a given type is a struct,
/// enum, union or an opaque type that has a struct declaration by the given name.
pub fn hasStruct(comptime T: type, comptime name: []const u8) Outcome {
    return hasDecl(T, name).andThen(struct {
        pub fn then() Outcome {
            return isType(@field(T, name), .Struct);
        }
    })
        .named(std.fmt.comptimePrint("hasStruct({}, {s})", .{ T, name }));
}

test "hasStruct" {
    comptime {
        try expect(hasStruct(u8, "a") == .Invalid);
        try expect(std.mem.eql(
            u8,
            hasStruct(u8, "a").Invalid.cause().Invalid.reason,
            "u8 is not a struct, enum, union or an opaque type",
        ));
        try expect(hasStruct(struct {}, "a") == .Invalid);
        try expect(hasStruct(struct {
            const a = struct {};
        }, "a") == .Valid);
        try expect(hasStruct(enum {
            a,
        }, "a") == .Invalid);
        try expect(hasStruct(enum {
            a,
            const b = struct {};
        }, "b") == .Valid);

        try expect(hasStruct(union(enum) {
            a: void,
        }, "a") == .Invalid);
        try expect(hasStruct(union(enum) {
            a: void,
            const b = struct {};
        }, "b") == .Valid);
    }
}

/// A contract that requires that a given type is a struct,
/// enum, union or an opaque type that has a function declaration by the given name.
pub fn hasFn(comptime T: type, comptime name: []const u8) Outcome {
    return hasDecl(T, name).andThen(struct {
        pub fn then() Outcome {
            return isType(@TypeOf(@field(T, name)), .Fn);
        }
    })
        .named(std.fmt.comptimePrint("hasFn({}, {s})", .{ T, name }));
}

test "hasFn" {
    comptime {
        try expect(hasFn(u8, "a") == .Invalid);
        try expect(std.mem.eql(
            u8,
            hasFn(u8, "a").Invalid.cause().Invalid.reason,
            "u8 is not a struct, enum, union or an opaque type",
        ));
        try expect(hasFn(struct {}, "a") == .Invalid);
        try expect(hasFn(struct {
            fn a() void {}
        }, "a") == .Valid);
        try expect(hasFn(enum {
            a,
        }, "a") == .Invalid);
        try expect(hasFn(enum {
            a,
            fn b() void {}
        }, "b") == .Valid);

        try expect(hasFn(union(enum) {
            a: void,
        }, "a") == .Invalid);
        try expect(hasFn(union(enum) {
            a: void,
            fn b() void {}
        }, "b") == .Valid);
    }
}

fn isEquivalent_(comptime A: type, comptime B: type) Outcome {
    return hasStruct(A, "contracts")
        .andThen(struct {
        pub fn then() Outcome {
            comptime {
                return hasFn(@field(A, "contracts"), "isEquivalent");
            }
        }
    })
        .andThen(struct {
        pub fn then() Outcome {
            return is(@TypeOf(A.contracts.isEquivalent), fn (type) bool);
        }
    })
        .andThen(struct {
        pub fn then() Outcome {
            return Outcome.init(A.contracts.isEquivalent(B), Invalid{
                .identifier = std.fmt.comptimePrint("{s}.contracts.isEquivalent({s})", .{ A, B }),
            });
        }
    });
}

/// A contract that requires that a given types A and B are a struct, enum, union or
/// an opaque type, and either A, or B, or both define `contracts` struct with `isEquivalent(type) bool`
/// function, and that function of either A or B returns true.
///
/// This is used to establish equivalency of otherwise unequal types:
///
/// ```
/// const A = struct {
///   pub const contracts = struct {
///     pub fn isEquivalent(comptime T: type) bool {
///       return T == B;
///     }
///   };
///   
///   pub const contracts = struct {
///     pub fn isEquivalent(comptime T: type) bool {
///       return T == B;
///     }
///   };
/// };
///
/// assert(isEquivalent(A, B) == .Valid);
/// ```
pub fn isEquivalent(comptime A: type, comptime B: type) Outcome {
    return isEquivalent_(A, B).orElse(isEquivalent_(B, A));
}

test "isEquivalent" {
    comptime {
        const Tequiv = struct {
            pub const contracts = struct {
                pub fn isEquivalent(comptime _: type) bool {
                    return true;
                }
            };
        };
        const Tnonequiv = struct {
            pub const contracts = struct {
                pub fn isEquivalent(comptime _: type) bool {
                    return false;
                }
            };
        };
        _ = Tequiv;
        _ = Tnonequiv;
        try expect(isEquivalent(Tequiv, Tnonequiv) == .Valid);
        try expect(isEquivalent(Tnonequiv, Tequiv) == .Valid);
        try expect(isEquivalent(Tnonequiv, Tnonequiv) == .Invalid);
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
