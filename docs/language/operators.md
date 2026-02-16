# Operators

Vole provides arithmetic, comparison, logical, bitwise, and type operators.

## Quick Reference

### Arithmetic

```vole,ignore
+      // Addition
-      // Subtraction
*      // Multiplication
/      // Division
%      // Modulo (remainder)
-x     // Negation (unary)
```

### Comparison

```vole,ignore
==     // Equal
!=     // Not equal
<      // Less than
>      // Greater than
<=     // Less or equal
>=     // Greater or equal
```

### Logical

```vole,ignore
&&     // Logical AND (short-circuit)
||     // Logical OR (short-circuit)
!      // Logical NOT
```

### Bitwise

```vole,ignore
&      // Bitwise AND
|      // Bitwise OR
^      // Bitwise XOR
~      // Bitwise NOT
<<     // Left shift
>>     // Right shift
```

### Compound Assignment

```vole,ignore
+=     // Add and assign
-=     // Subtract and assign
*=     // Multiply and assign
/=     // Divide and assign
%=     // Modulo and assign
```

### Type Operators

```vole,ignore
is     // Type check (e.g. x is i64)
```

### Optional Operators

```vole,ignore
??     // Null coalescing
?.     // Optional chaining
```

## In Depth

### Arithmetic Operators

Basic math operations:

```vole
tests {
    test "arithmetic" {
        let a = 10
        let b = 3

        assert(a + b == 13)
        assert(a - b == 7)
        assert(a * b == 30)
        assert(a / b == 3)
        assert(a % b == 1)
    }
}
```

Unary negation:

```vole
tests {
    test "negation" {
        let x = 5
        assert(-x == -5)
        assert(-(-x) == 5)
        assert(--5 == 5)
    }
}
```

### Integer vs Float Division

Integer division truncates toward zero:

```vole
tests {
    test "integer division truncates" {
        assert(7 / 2 == 3)
        assert(-7 / 2 == -3)
    }
}
```

For decimal results, use floats:

```vole
tests {
    test "float division" {
        let result = 7.0 / 2.0
        assert(result == 3.5)
    }
}
```

Integer modulo uses remainder semantics (sign follows dividend):

```vole
tests {
    test "modulo semantics" {
        assert(10 % 3 == 1)
        assert(-7 % 2 == -1)
        assert(7 % 2 == 1)
    }
}
```

### Operator Precedence

Multiplication and division bind tighter than addition and subtraction:

```vole
tests {
    test "precedence" {
        assert(2 + 3 * 4 == 14)
        assert((2 + 3) * 4 == 20)
        assert(10 - 2 * 3 == 4)
    }
}
```

### Comparison Operators

Compare values of the same type:

```vole
tests {
    test "comparisons" {
        assert(5 == 5)
        assert(5 != 3)
        assert(3 < 5)
        assert(5 > 3)
        assert(3 <= 3)
        assert(5 >= 5)
    }
}
```

String equality:

```vole
tests {
    test "string equality" {
        let a = "apple"
        assert(a == "apple")
        assert(a != "banana")
    }
}
```

Semantic equality works across numeric types:

```vole
tests {
    test "cross-type equality" {
        let a: i32 = 42
        let b: i64 = 42
        assert(a == b)

        let c: i32 = 42
        let d: f64 = 42.0
        assert(c == d)
    }
}
```

### Logical Operators

Boolean logic with `&&`, `||`, and `!`:

```vole
tests {
    test "logical operators" {
        assert(true && true)
        assert(!(true && false))
        assert(!(false && true))
        assert(!(false && false))

        assert(true || true)
        assert(true || false)
        assert(false || true)
        assert(!(false || false))

        assert(!false)
        assert(!!true)
    }
}
```

Short-circuit evaluation -- the right operand is not evaluated if the result is already determined:

```vole
tests {
    test "short-circuit AND" {
        let result = false && true
        assert(result == false)
    }

    test "short-circuit OR" {
        let result = true || false
        assert(result == true)
    }
}
```

Common patterns with logical operators in conditions:

```vole
tests {
    test "logical in conditions" {
        let x = 5
        let y = 10
        let mut result = false
        if x > 0 && y > 0 {
            result = true
        }
        assert(result == true)

        let mut either = false
        if x > 100 || y > 0 {
            either = true
        }
        assert(either == true)

        let a = 5
        let b = 10
        let c = -1
        let mut combined = false
        if (a > 0 && b > 0) || c > 0 {
            combined = true
        }
        assert(combined == true)
    }
}
```

### Bitwise Operators

Operate on individual bits:

```vole
tests {
    test "bitwise operators" {
        // AND
        assert((12 & 10) == 8)

        // OR
        assert((12 | 10) == 14)

        // XOR
        assert((12 ^ 10) == 6)

        // XOR with same value gives zero
        assert((255 ^ 255) == 0)
    }
}
```

Shift operators:

```vole
tests {
    test "shift operators" {
        assert((1 << 0) == 1)
        assert((1 << 1) == 2)
        assert((1 << 4) == 16)
        assert((16 >> 1) == 8)
        assert((16 >> 4) == 1)
    }
}
```

Bitwise NOT:

```vole
tests {
    test "bitwise NOT" {
        let y = 42
        assert((~~y) == y)
    }
}
```

Common bitwise patterns:

```vole
tests {
    test "bitwise patterns" {
        // Set bit 3: 0 | (1 << 3) = 8
        let x = 0 | (1 << 3)
        assert(x == 8)

        // Clear bit 3: 15 & ~8 = 7
        let y = 15 & ~(1 << 3)
        assert(y == 7)

        // Toggle bit 2: 10 ^ 4 = 14
        let z = 10 ^ (1 << 2)
        assert(z == 14)
    }
}
```

Masking to extract bytes:

```vole
tests {
    test "byte masking" {
        let value = 43981

        // Extract low byte
        let low = value & 255
        assert(low == 205)

        // Extract high byte
        let high = (value >> 8) & 255
        assert(high == 171)
    }
}
```

Binary literals can be used for clarity:

```vole
tests {
    test "binary literals" {
        let result = 0b1100 & 0b1010
        assert(result == 0b1000)
    }
}
```

### Compound Assignment Operators

Modify a mutable variable in place:

```vole
tests {
    test "compound assignment" {
        let mut x = 10
        x += 5
        assert(x == 15)

        x -= 3
        assert(x == 12)

        x *= 2
        assert(x == 24)

        x /= 4
        assert(x == 6)

        x %= 4
        assert(x == 2)
    }
}
```

Works with array indexing:

```vole
tests {
    test "compound assignment on array" {
        let mut arr = [1, 2, 3]
        arr[0] += 10
        assert(arr[0] == 11)
    }
}
```

### Type Operators

Check type at runtime with `is`:

```vole
tests {
    test "is operator" {
        let x: i64 | string = 5
        assert(x is i64)
        assert(!(x is string))
    }
}
```

Type narrowing in if branches -- after an `is` check, the variable is narrowed to that type:

```vole
tests {
    test "type narrowing with is" {
        let x: i64 | string = "hello"
        if x is string {
            let len = x.length()
            assert(len == 5)
        } else {
            assert(false)
        }
    }
}
```

Type narrowing also works in `when` expressions:

```vole
tests {
    test "is in when expression" {
        let x: i64 | string = "hello"
        let result = when {
            x is string => x.length()
            _ => 0
        }
        assert(result == 5)
    }
}
```

### Null Coalescing Operator

Provide a default for optional values with `??`:

```vole
tests {
    test "null coalescing" {
        let x: i32? = 42
        let result = x ?? 0
        assert(result == 42)

        let y: i32? = nil
        let result2 = y ?? 99
        assert(result2 == 99)
    }
}
```

Chain multiple fallbacks:

```vole
tests {
    test "null coalescing chain" {
        let a: i32? = nil
        let b: i32? = nil
        let c: i32? = 42

        let result = a ?? b ?? c ?? 0
        assert(result == 42)
    }
}
```

### Optional Chaining

Safely access fields on optional values with `?.`:

```vole
class Person {
    name: string,
    age: i32,
}

tests {
    test "optional chaining non-nil" {
        let p: Person? = Person { name: "Alice", age: 30 }
        let name = p?.name
        assert((name ?? "") == "Alice")
    }

    test "optional chaining nil" {
        let p: Person? = nil
        let name = p?.name
        assert(name is nil)
    }

    test "optional chaining with null coalescing" {
        let p: Person? = nil
        let name = p?.name ?? "Unknown"
        assert(name == "Unknown")
    }
}
```

Nested optional chaining:

```vole
class Employee {
    name: string,
}

class Company {
    name: string,
    ceo: Employee?,
}

tests {
    test "nested optional chaining" {
        let c: Company? = Company {
            name: "Acme",
            ceo: Employee { name: "Eve" },
        }
        let ceoName = c?.ceo?.name
        assert((ceoName ?? "") == "Eve")
    }

    test "nested optional chaining nil" {
        let c: Company? = Company {
            name: "Startup",
            ceo: nil,
        }
        let ceoName = c?.ceo?.name ?? "No CEO"
        assert(ceoName == "No CEO")
    }
}
```

### Discard Operator

Use `_ =` to explicitly discard a value (useful for calling functions for side effects):

```vole
func get_value() -> i64 => 42

tests {
    test "discard value" {
        _ = get_value()
        assert(true)
    }
}
```

### String Concatenation

The `+` operator concatenates strings:

```vole
tests {
    test "string concatenation" {
        let result = "a" + "b" + "c"
        assert(result == "abc")
    }
}
```

String interpolation is also available using `{}` inside string literals:

```vole
tests {
    test "string interpolation" {
        let name = "world"
        let greeting = "hello {name}"
        assert(greeting == "hello world")
    }
}
```

### Operator Precedence

From highest to lowest:

```vole,ignore
1.  Unary: -, !, ~
2.  Multiplicative: *, /, %
3.  Additive: +, -
4.  Shift: <<, >>
5.  Comparison: <, >, <=, >=
6.  Equality: ==, !=
7.  Bitwise AND: &
8.  Bitwise XOR: ^
9.  Bitwise OR: |
10. Logical AND: &&
11. Logical OR: ||
12. Null coalescing: ??
```

Use parentheses for clarity:

```vole
tests {
    test "parentheses for clarity" {
        let result = (2 + 3) * 4
        assert(result == 20)

        let check = (5 > 0) && (10 < 20)
        assert(check == true)
    }
}
```
