# Collections

Vole provides built-in arrays and a standard library with generic `Map`, `Set`, and `Buffer` types.

## Quick Reference

| Type | Import | Description |
|------|--------|-------------|
| `[T]` | Built-in | Dynamic array of elements |
| `Map<K, V>` | `std:collections/map` | Hash map (key-value pairs) |
| `Set<T>` | `std:collections/set` | Hash set (unique elements) |
| `Buffer` | Built-in | Growable byte buffer |
| `Array.filled` | `std:array` | Create pre-filled arrays |

## Arrays

Arrays are ordered, dynamically-sized collections of a single type. For full type syntax, see [Types](types.md).

### Creating Arrays

```vole
tests {
    test "array creation" {
        let nums = [1, 2, 3, 4, 5]
        assert(nums.length() == 5)

        let names: [string] = ["Alice", "Bob"]
        assert(names.length() == 2)

        let empty: [i64] = []
        assert(empty.length() == 0)
    }
}
```

### Indexing and Length

```vole
tests {
    test "array indexing" {
        let arr = [10, 20, 30]
        assert(arr[0] == 10)
        assert(arr[2] == 30)
        assert(arr.length() == 3)
    }
}
```

### Pushing Elements

Arrays grow dynamically with `push`:

```vole
tests {
    test "array push" {
        let arr: [i64] = []
        arr.push(1)
        arr.push(2)
        arr.push(3)
        assert(arr.length() == 3)
        assert(arr[0] == 1)
        assert(arr[2] == 3)
    }
}
```

### Iterating

Arrays work directly with `for` loops and the iterator pipeline:

```vole
tests {
    test "array for loop" {
        var sum = 0
        for x in [1, 2, 3] {
            sum = sum + x
        }
        assert(sum == 6)
    }

    test "array iterator" {
        let doubled = [1, 2, 3].iter().map((x) => x * 2).collect()
        assert(doubled[0] == 2)
        assert(doubled[2] == 6)
    }
}
```

See [Iterators](iterators.md) for the full iterator API.

### Nested Arrays

```vole
tests {
    test "nested arrays" {
        let matrix = [[1, 2], [3, 4]]
        assert(matrix[0][0] == 1)
        assert(matrix[1][1] == 4)
    }
}
```

### Arrays with Union and Optional Elements

Arrays can hold union types, optional types, and sentinels:

```vole
sentinel Empty

tests {
    test "optional array" {
        let arr: [i64?] = []
        arr.push(42)
        arr.push(nil)
        arr.push(99)
        assert(arr.length() == 3)
        assert(arr[0] != nil)
        assert(arr[1] == nil)
    }

    test "union array" {
        let arr: [i64 | string] = [1, "two", 3, "four"]
        var nums: i64 = 0
        for item in arr {
            if item is i64 {
                nums = nums + item
            }
        }
        assert(nums == 4)
    }

    test "sentinel array" {
        let arr: [i64 | Empty] = []
        arr.push(42)
        arr.push(Empty)
        assert(arr[0] is i64)
        assert(arr[1] is Empty)
    }
}
```

### Array.filled

The `Array.filled` utility creates arrays pre-filled with a value. Import from `std:array`:

```vole
let { Array } = import "std:array"

tests {
    test "filled with zeros" {
        let arr = Array.filled<i64>(5, 0)
        assert(arr.length() == 5)
        assert(arr[0] == 0)
        assert(arr[4] == 0)
    }

    test "filled with strings" {
        let arr = Array.filled<string>(3, "x")
        assert(arr.length() == 3)
        assert(arr[0] == "x")
        assert(arr[2] == "x")
    }
}
```

---

## Map<K, V>

`Map<K, V>` is a generic hash map. Keys must implement `Hashable + Equatable`. Primitive types (`i64`, `string`) implement these automatically.

Import from `std:collections/map`:

```vole
let { Map } = import "std:collections/map"

tests {
    test "map basics" {
        let m = Map.new<string, i64>()
        m.set("alpha", 1)
        m.set("beta", 2)
        assert(m.len() == 2)
        assert((m.get("alpha") ?? 0) == 1)
        assert((m.get("beta") ?? 0) == 2)
        assert(m.get("missing") == nil)
    }
}
```

### API Reference

| Method | Signature | Description |
|--------|-----------|-------------|
| `Map.new()` | `() -> Map<K, V>` | Create empty map |
| `Map.with_capacity(n)` | `(i64) -> Map<K, V>` | Create with initial capacity |
| `.set(key, value)` | `(K, V) -> void` | Insert or update a key-value pair |
| `.get(key)` | `(K) -> V?` | Get value for key (nil if missing) |
| `.contains_key(key)` | `(K) -> bool` | Check if key exists |
| `.remove(key)` | `(K) -> V?` | Remove key, return value (nil if missing) |
| `.len()` | `() -> i64` | Number of entries |
| `.is_empty()` | `() -> bool` | True if no entries |
| `.clear()` | `() -> void` | Remove all entries |
| `.keys()` | `() -> Iterator<K>` | Iterator over keys |
| `.values()` | `() -> Iterator<V>` | Iterator over values |
| `.entries()` | `() -> Iterator<[K, V]>` | Iterator over [key, value] pairs |
| `.iter()` | `() -> Iterator<[K, V]>` | Same as `.entries()` |

### Creating a Map

```vole
let { Map } = import "std:collections/map"

tests {
    test "map constructors" {
        let m1 = Map.new<i64, i64>()
        assert(m1.len() == 0)
        assert(m1.is_empty())

        let m2 = Map.with_capacity<i64, string>(100)
        assert(m2.len() == 0)
        m2.set(1, "one")
        assert(m2.len() == 1)
    }
}
```

### Get and Set

`get` returns `V?` -- the value if found, or `nil` if the key is missing. Use `??` to provide a default:

```vole
let { Map } = import "std:collections/map"

tests {
    test "map get returns optional" {
        let m = Map.new<i64, i64>()
        m.set(1, 100)
        m.set(2, 200)

        assert(m.get(1) == 100)
        assert(m.get(2) == 200)
        assert(m.get(999) == nil)
    }

    test "map get with coalesce" {
        let m = Map.new<i64, string>()
        m.set(1, "one")
        let result = m.get(999) ?? "default"
        assert(result == "default")
    }
}
```

Setting the same key again updates the value:

```vole
let { Map } = import "std:collections/map"

tests {
    test "map update existing key" {
        let m = Map.new<i64, i64>()
        m.set(1, 100)
        m.set(1, 999)
        assert(m.len() == 1)
        assert(m.get(1) == 999)
    }
}
```

### Remove

`remove` returns the removed value (or `nil` if the key was not present):

```vole
let { Map } = import "std:collections/map"

tests {
    test "map remove" {
        let m = Map.new<i64, i64>()
        m.set(1, 100)
        m.set(2, 200)

        let removed = m.remove(1)
        assert(removed == 100)
        assert(m.len() == 1)
        assert(!m.contains_key(1))
        assert(m.contains_key(2))
    }

    test "map remove missing" {
        let m = Map.new<i64, i64>()
        assert(m.remove(999) == nil)
    }
}
```

### Iterating Over a Map

Maps provide `keys()`, `values()`, and `entries()` iterators:

```vole
let { Map } = import "std:collections/map"

tests {
    test "map keys iteration" {
        let m = Map.new<i64, i64>()
        m.set(1, 10)
        m.set(2, 20)
        m.set(3, 30)

        var sum = 0
        for k in m.keys() {
            sum = sum + k
        }
        assert(sum == 6)
    }

    test "map values iteration" {
        let m = Map.new<i64, i64>()
        m.set(1, 10)
        m.set(2, 20)
        m.set(3, 30)

        var sum = 0
        for v in m.values() {
            sum = sum + v
        }
        assert(sum == 60)
    }

    test "map iterator counts" {
        let m = Map.new<i64, i64>()
        m.set(1, 10)
        m.set(2, 20)
        assert(m.keys().count() == 2)
        assert(m.values().count() == 2)
        assert(m.entries().count() == 2)
    }
}
```

### Maps with Custom Key Types

To use a class as a map key, implement `Hashable` and `Equatable`:

```vole
let { Map } = import "std:collections/map"

class Point {
    x: i64,
    y: i64,
}

extend Point with Hashable {
    func hash() -> i64 {
        return self.x * 31 + self.y
    }
}

extend Point with Equatable {
    func equals(other: Point) -> bool {
        return self.x == other.x && self.y == other.y
    }
}

tests {
    test "map with custom key" {
        let m = Map.new<Point, string>()
        let p1 = Point { x: 1, y: 2 }
        let p2 = Point { x: 3, y: 4 }

        m.set(p1, "origin-near")
        m.set(p2, "middle")

        assert(m.len() == 2)
        assert((m.get(p1) ?? "") == "origin-near")

        // Equal-but-different instance lookup
        let p1_copy = Point { x: 1, y: 2 }
        assert((m.get(p1_copy) ?? "") == "origin-near")
        assert(m.contains_key(p1_copy))
    }
}
```

### Maps with Class Values

Classes (including those with string fields) work as map values:

```vole
let { Map } = import "std:collections/map"

class Person {
    name: string,
    age: i64,
}

tests {
    test "map with class values" {
        let m = Map.new<i64, Person>()
        m.set(1, Person { name: "Alice", age: 30 })
        m.set(2, Person { name: "Bob", age: 25 })

        let got = m.get(1) ?? Person { name: "", age: 0 }
        assert(got.age == 30)
        let n = got.name
        assert(n == "Alice")
    }
}
```

---

## Set<T>

`Set<T>` is a generic hash set. Elements must implement `Hashable + Equatable`. Primitive types (`i64`, `string`) implement these automatically.

Import from `std:collections/set`:

```vole
let { Set } = import "std:collections/set"

tests {
    test "set basics" {
        let s = Set.new<i64>()
        assert(s.add(1))
        assert(s.add(2))
        assert(s.add(3))
        assert(s.len() == 3)
        assert(s.contains(1))
        assert(!s.contains(4))
    }
}
```

### API Reference

| Method | Signature | Description |
|--------|-----------|-------------|
| `Set.new()` | `() -> Set<T>` | Create empty set |
| `Set.with_capacity(n)` | `(i64) -> Set<T>` | Create with initial capacity |
| `.add(value)` | `(T) -> bool` | Add element; returns `true` if new, `false` if duplicate |
| `.contains(value)` | `(T) -> bool` | Check if element exists |
| `.remove(value)` | `(T) -> bool` | Remove element; returns `true` if found |
| `.len()` | `() -> i64` | Number of elements |
| `.is_empty()` | `() -> bool` | True if no elements |
| `.clear()` | `() -> void` | Remove all elements |
| `.iter()` | `() -> Iterator<T>` | Iterator over elements |
| `.union(other)` | `(Set<T>) -> Set<T>` | New set with elements from both |
| `.intersection(other)` | `(Set<T>) -> Set<T>` | New set with common elements |
| `.difference(other)` | `(Set<T>) -> Set<T>` | New set with elements only in self |
| `.symmetric_difference(other)` | `(Set<T>) -> Set<T>` | New set with elements in exactly one |
| `.is_subset(other)` | `(Set<T>) -> bool` | True if all elements are in other |
| `.is_superset(other)` | `(Set<T>) -> bool` | True if other is a subset of self |
| `.is_disjoint(other)` | `(Set<T>) -> bool` | True if no shared elements |

### Add and Contains

`add` returns a boolean: `true` if the element was new, `false` if it was already present:

```vole
let { Set } = import "std:collections/set"

tests {
    test "set add returns bool" {
        let s = Set.new<i64>()
        assert(s.add(42))     // new element: true
        assert(!s.add(42))    // duplicate: false
        assert(s.len() == 1)
        assert(s.contains(42))
    }
}
```

### Remove

`remove` returns `true` if the element was found and removed:

```vole
let { Set } = import "std:collections/set"

tests {
    test "set remove" {
        let s = Set.new<i64>()
        _ = s.add(1)
        _ = s.add(2)
        _ = s.add(3)

        assert(s.remove(2))
        assert(s.len() == 2)
        assert(!s.contains(2))
        assert(s.contains(1))
        assert(s.contains(3))
    }

    test "set remove missing" {
        let s = Set.new<i64>()
        assert(!s.remove(999))
    }
}
```

### Set Operations

Sets support the standard mathematical set operations. Each returns a new set:

```vole
let { Set } = import "std:collections/set"

tests {
    test "set union" {
        let a = Set.new<i64>()
        _ = a.add(1)
        _ = a.add(2)

        let b = Set.new<i64>()
        _ = b.add(2)
        _ = b.add(3)

        let u = a.union(b)
        assert(u.len() == 3)
        assert(u.contains(1))
        assert(u.contains(2))
        assert(u.contains(3))
    }

    test "set intersection" {
        let a = Set.new<i64>()
        _ = a.add(1)
        _ = a.add(2)
        _ = a.add(3)

        let b = Set.new<i64>()
        _ = b.add(2)
        _ = b.add(3)
        _ = b.add(4)

        let i = a.intersection(b)
        assert(i.len() == 2)
        assert(i.contains(2))
        assert(i.contains(3))
        assert(!i.contains(1))
    }

    test "set difference" {
        let a = Set.new<i64>()
        _ = a.add(1)
        _ = a.add(2)
        _ = a.add(3)

        let b = Set.new<i64>()
        _ = b.add(2)
        _ = b.add(3)
        _ = b.add(4)

        let d = a.difference(b)
        assert(d.len() == 1)
        assert(d.contains(1))
        assert(!d.contains(2))
    }

    test "set symmetric difference" {
        let a = Set.new<i64>()
        _ = a.add(1)
        _ = a.add(2)
        _ = a.add(3)

        let b = Set.new<i64>()
        _ = b.add(2)
        _ = b.add(3)
        _ = b.add(4)

        let sd = a.symmetric_difference(b)
        assert(sd.len() == 2)
        assert(sd.contains(1))
        assert(sd.contains(4))
        assert(!sd.contains(2))
    }
}
```

### Subset, Superset, and Disjoint

```vole
let { Set } = import "std:collections/set"

tests {
    test "set subset and superset" {
        let a = Set.new<i64>()
        _ = a.add(1)
        _ = a.add(2)

        let b = Set.new<i64>()
        _ = b.add(1)
        _ = b.add(2)
        _ = b.add(3)

        assert(a.is_subset(b))
        assert(!b.is_subset(a))
        assert(b.is_superset(a))
        assert(!a.is_superset(b))
    }

    test "set disjoint" {
        let a = Set.new<i64>()
        _ = a.add(1)
        _ = a.add(2)

        let b = Set.new<i64>()
        _ = b.add(3)
        _ = b.add(4)

        assert(a.is_disjoint(b))

        let c = Set.new<i64>()
        _ = c.add(2)
        _ = c.add(3)

        assert(!a.is_disjoint(c))
    }
}
```

### Iterating Over a Set

```vole
let { Set } = import "std:collections/set"

tests {
    test "set iteration" {
        let s = Set.new<i64>()
        _ = s.add(10)
        _ = s.add(20)
        _ = s.add(30)

        assert(s.iter().count() == 3)

        var sum = 0
        for x in s.iter() {
            sum = sum + x
        }
        assert(sum == 60)
    }
}
```

### Sets with String Elements

```vole
let { Set } = import "std:collections/set"

tests {
    test "set of strings" {
        let s = Set.new<string>()
        assert(s.add("hello"))
        assert(s.add("world"))
        assert(!s.add("hello"))
        assert(s.len() == 2)
        assert(s.contains("hello"))
        assert(!s.contains("foo"))
    }
}
```

### Sets with Custom Types

Like maps, custom set elements need `Hashable` and `Equatable`:

```vole
let { Set } = import "std:collections/set"

class Color {
    r: i64,
    g: i64,
    b: i64,
}

extend Color with Hashable {
    func hash() -> i64 {
        return self.r * 65536 + self.g * 256 + self.b
    }
}

extend Color with Equatable {
    func equals(other: Color) -> bool {
        return self.r == other.r && self.g == other.g && self.b == other.b
    }
}

tests {
    test "set with custom type" {
        let s = Set.new<Color>()
        let red = Color { r: 255, g: 0, b: 0 }
        let green = Color { r: 0, g: 255, b: 0 }

        assert(s.add(red))
        assert(s.add(green))
        assert(s.len() == 2)

        // Equal-but-different instance
        let red2 = Color { r: 255, g: 0, b: 0 }
        assert(s.contains(red2))
        assert(!s.add(red2))
    }
}
```

---

## Buffer

`Buffer` is a growable byte buffer backed by native memory. It is useful for low-level byte manipulation and binary data. `Buffer` is a built-in type and requires no import.

### API Reference

| Method | Signature | Description |
|--------|-----------|-------------|
| `Buffer.new()` | `() -> Buffer` | Create empty buffer |
| `Buffer.with_capacity(n)` | `(i64) -> Buffer` | Create with reserved capacity |
| `Buffer.from_string(s)` | `(string) -> Buffer` | Create from string bytes |
| `.append_byte(b)` | `(i64) -> void` | Append a byte (masked to low 8 bits) |
| `.append(buf)` | `(Buffer) -> void` | Append another buffer |
| `.get(index)` | `(i64) -> i64` | Get byte at index (-1 if out of bounds) |
| `.set(index, value)` | `(i64, i64) -> void` | Set byte at index (masked to low 8 bits) |
| `.slice(start, end)` | `(i64, i64) -> Buffer` | Extract sub-buffer (end = -1 means to end) |
| `.to_string_raw()` | `() -> string` | Convert buffer to string |
| `.length()` | `() -> i64` | Number of bytes |
| `.capacity()` | `() -> i64` | Allocated capacity |
| `.clear()` | `() -> void` | Remove all bytes (preserves capacity) |
| `.equals(other)` | `(Buffer) -> bool` | Byte-for-byte equality |

### Creating Buffers

```vole
tests {
    test "buffer constructors" {
        let empty = Buffer.new()
        assert(empty.length() == 0)

        let reserved = Buffer.with_capacity(16)
        assert(reserved.length() == 0)
        assert(reserved.capacity() >= 16)

        let from_str = Buffer.from_string("hello")
        assert(from_str.length() == 5)
    }
}
```

### Reading and Writing Bytes

```vole
tests {
    test "buffer byte operations" {
        let buf = Buffer.new()
        buf.append_byte(72)   // 'H'
        buf.append_byte(105)  // 'i'
        assert(buf.length() == 2)
        assert(buf.get(0) == 72)
        assert(buf.get(1) == 105)

        // Out of bounds returns -1
        assert(buf.get(99) == -1)
    }

    test "buffer set byte" {
        let buf = Buffer.from_string("abc")
        buf.set(0, 65)  // 'A'
        assert(buf.get(0) == 65)
        assert(buf.to_string_raw() == "Abc")
    }

    test "buffer byte masking" {
        let buf = Buffer.new()
        buf.append_byte(256 + 65)  // should store 65 ('A')
        assert(buf.get(0) == 65)
    }
}
```

### Appending Buffers

```vole
tests {
    test "buffer append" {
        let a = Buffer.from_string("hello")
        let b = Buffer.from_string(" world")
        a.append(b)
        assert(a.length() == 11)
        assert(a.to_string_raw() == "hello world")
    }
}
```

### Slicing

```vole
tests {
    test "buffer slice" {
        let buf = Buffer.from_string("hello world")
        let hello = buf.slice(0, 5)
        assert(hello.to_string_raw() == "hello")

        let world = buf.slice(6, 11)
        assert(world.to_string_raw() == "world")

        // -1 means to end
        let rest = buf.slice(6, -1)
        assert(rest.to_string_raw() == "world")
    }
}
```

### String Conversion

```vole
tests {
    test "buffer to string roundtrip" {
        let original = "The quick brown fox"
        let buf = Buffer.from_string(original)
        let result = buf.to_string_raw()
        assert(result == original)
    }

    test "buffer manual construction" {
        let buf = Buffer.new()
        buf.append_byte(86)   // 'V'
        buf.append_byte(111)  // 'o'
        buf.append_byte(108)  // 'l'
        buf.append_byte(101)  // 'e'
        assert(buf.to_string_raw() == "Vole")
    }
}
```

### Equality

```vole
tests {
    test "buffer equality" {
        let a = Buffer.from_string("hello")
        let b = Buffer.from_string("hello")
        assert(a.equals(b))

        let c = Buffer.from_string("world")
        assert(!a.equals(c))

        let d = Buffer.new()
        let e = Buffer.new()
        assert(d.equals(e))
    }
}
```

### Clear

```vole
tests {
    test "buffer clear" {
        let buf = Buffer.from_string("hello")
        let cap_before = buf.capacity()
        buf.clear()
        assert(buf.length() == 0)
        assert(buf.capacity() == cap_before)

        // Reuse after clear
        buf.append_byte(65)
        assert(buf.length() == 1)
        assert(buf.get(0) == 65)
    }
}
```

---

## See Also

- [Types](types.md) - Type system overview, including array syntax
- [Iterators](iterators.md) - Iterator methods available on collection iterators
- [Interfaces](interfaces.md) - Defining `Hashable` and `Equatable`
- [Generics](generics.md) - Generic type parameters and constraints
