# Concurrency

Vole provides cooperative concurrency through tasks and channels. Tasks are lightweight green threads scheduled on a M:1 scheduler. Channels are typed, bounded message queues for safe communication between tasks.

## Quick Reference

| API | Description |
|-----|-------------|
| `Task.run(fn)` | Spawn a task, returns a handle |
| `task.join()` | Block until the task completes, return its result |
| `task.cancel()` | Request cooperative cancellation |
| `task.is_done()` | Check if the task has completed |
| `Task.all(fns)` | Spawn all closures, collect results in order |
| `Task.parallel(items, fn)` | Transform each item in parallel |
| `Task.stream(producer)` | Create a streaming iterator from a producer |
| `Task.state(initial, handler)` | Create a stateful actor |
| `Task.select2(ch1, ch2, timeout)` | Wait on two channels |
| `Task.select3(ch1, ch2, ch3, timeout)` | Wait on three channels |
| `Channel.new()` | Create an unbuffered channel |
| `Channel.buffered(n)` | Create a buffered channel with capacity n |
| `ch.send(value)` | Send a value (returns bool) |
| `ch.receive()` | Blocking receive |
| `ch.try_receive()` | Non-blocking receive (returns `T \| Done`) |
| `ch.close()` | Close the channel |
| `ch.is_closed()` | Check if closed |
| `ch.iter()` | Drain channel as an iterator |

## Importing

The concurrency module is imported from `std:task`:

```vole
let { Task, Channel } = import "std:task"

tests {
    test "basic import" {
        let t = Task.run(() -> i64 => { return 1 })
        assert(t.join() == 1)
    }
}
```

For select operations, also import `SelectResult` and `Duration`:

```vole
let { Task, Channel, SelectResult } = import "std:task"
let { Duration } = import "std:time"

tests {
    test "select import" {
        let ch1 = Channel.buffered<i64>(4)
        let ch2 = Channel.buffered<i64>(4)
        ch1.send(10)
        let r = Task.select2(ch1, ch2, Duration.zero())
        assert(!r.timed_out)
        assert(r.value == 10)
    }
}
```

## Tasks

### Spawning and Joining

`Task.run` takes a closure and returns a `Task<T>` handle. The closure runs on the cooperative scheduler. Call `.join()` to block until the task completes and retrieve its result:

```vole
let { Task } = import "std:task"

tests {
    test "run and join" {
        let t = Task.run(() -> i64 => { return 42 })
        assert(t.join() == 42)
    }

    test "join returns captured value" {
        let x = 10
        let t = Task.run(() -> i64 => { return x + 5 })
        assert(t.join() == 15)
    }
}
```

Tasks work with any `Sendable` type -- `i64`, `f64`, `bool`, `string`, structs, and transferable classes:

```vole
let { Task } = import "std:task"

tests {
    test "task with string result" {
        let t = Task.run(() -> string => { return "hello" })
        assert(t.join() == "hello")
    }

    test "task with f64 result" {
        let t = Task.run(() -> f64 => { return 3.14 })
        assert(t.join() == 3.14)
    }

    test "task with bool result" {
        let t = Task.run(() -> bool => { return true })
        assert(t.join())
    }
}
```

### Join is Idempotent

Calling `.join()` multiple times returns the same result:

```vole
let { Task } = import "std:task"

tests {
    test "join is idempotent" {
        let t = Task.run(() -> i64 => { return 42 })
        let first = t.join()
        let second = t.join()
        assert(first == 42)
        assert(second == 42)
    }
}
```

### is_done and cancel

Check whether a task has completed with `.is_done()`, or request cooperative cancellation with `.cancel()`:

```vole
let { Task } = import "std:task"

tests {
    test "is_done after join" {
        let t = Task.run(() -> i64 => { return 99 })
        let result = t.join()
        assert(t.is_done())
        assert(result == 99)
    }

    test "cancel marks task as done" {
        let t = Task.run(() -> i64 => { return 77 })
        t.cancel()
        assert(t.is_done())
    }

    test "multiple cancel is safe" {
        let t = Task.run(() -> i64 => { return 99 })
        t.cancel()
        t.cancel()
        t.cancel()
        assert(t.is_done())
    }
}
```

### Multiple Tasks

Multiple tasks can run concurrently:

```vole
let { Task } = import "std:task"

tests {
    test "multiple tasks" {
        let t1 = Task.run(() -> i64 => { return 1 })
        let t2 = Task.run(() -> i64 => { return 2 })
        let t3 = Task.run(() -> i64 => { return 3 })
        assert(t1.join() + t2.join() + t3.join() == 6)
    }
}
```

## Task.all

`Task.all` spawns one task per closure and collects results in order. It returns an array with the same length and ordering as the input:

```vole
let { Task } = import "std:task"

tests {
    test "all runs closures concurrently" {
        let fns: [() -> i64] = [
            () -> i64 => { return 1 },
            () -> i64 => { return 2 },
            () -> i64 => { return 3 },
        ]
        let results = Task.all(fns)
        assert(results.length() == 3)
        assert(results[0] == 1)
        assert(results[1] == 2)
        assert(results[2] == 3)
    }

    test "all with captured values" {
        let base = 10
        let fns: [() -> i64] = [
            () -> i64 => { return base + 1 },
            () -> i64 => { return base + 2 },
        ]
        let results = Task.all(fns)
        assert(results[0] == 11)
        assert(results[1] == 12)
    }

    test "all with empty array" {
        let fns: [() -> i64] = []
        let results = Task.all(fns)
        assert(results.length() == 0)
    }
}
```

Works with non-i64 types:

```vole
let { Task } = import "std:task"

tests {
    test "all with strings" {
        let fns: [() -> string] = [
            () -> string => { return "a" },
            () -> string => { return "b" },
            () -> string => { return "c" },
        ]
        let out = Task.all(fns)
        assert(out.length() == 3)
        assert(out[0] == "a")
        assert(out[1] == "b")
        assert(out[2] == "c")
    }

    test "all with f64" {
        let fns: [() -> f64] = [
            () -> f64 => { return 1.1 },
            () -> f64 => { return 2.2 },
            () -> f64 => { return 3.3 },
        ]
        let results = Task.all(fns)
        assert(results.length() == 3)
        assert(results[0] == 1.1)
        assert(results[1] == 2.2)
        assert(results[2] == 3.3)
    }
}
```

## Task.parallel

`Task.parallel` transforms each item in an array concurrently, returning results in order. It requires a type parameter:

```vole
let { Task } = import "std:task"

tests {
    test "parallel doubles values" {
        let results = Task.parallel<i64>([1, 2, 3, 4, 5], (x: i64) -> i64 => { return x * 2 })
        assert(results.length() == 5)
        var sum = 0
        for v in results.iter() {
            sum = sum + v
        }
        assert(sum == 30)
    }

    test "parallel with strings" {
        let out = Task.parallel<string>(
            ["ax", "by", "cz"],
            (s: string) -> string => { return s + "!" },
        )
        assert(out.length() == 3)
        assert(out[0] == "ax!")
        assert(out[1] == "by!")
        assert(out[2] == "cz!")
    }
}
```

## Task.stream

`Task.stream` creates a streaming iterator backed by a producer task. The producer receives an `emit` callback to send values. The returned iterator yields values until the producer finishes:

```vole
let { Task } = import "std:task"

tests {
    test "stream produces values consumed by for loop" {
        var sum = 0
        let s = Task.stream((emit: (i64) -> void) => {
            emit(1)
            emit(2)
            emit(3)
        })
        for v in s {
            sum = sum + v
        }
        assert(sum == 6)
    }

    test "stream works with collect" {
        let s = Task.stream((emit: (i64) -> void) => {
            emit(10)
            emit(20)
            emit(30)
        })
        let result = s.collect()
        assert(result.length() == 3)
        assert(result[0] == 10)
        assert(result[1] == 20)
        assert(result[2] == 30)
    }

    test "empty stream produces no values" {
        let s = Task.stream((emit: (i64) -> void) => {
            // produce nothing
        })
        let result = s.collect()
        assert(result.length() == 0)
    }
}
```

Streams work with non-i64 types:

```vole
let { Task } = import "std:task"

tests {
    test "stream with strings" {
        let s = Task.stream((emit: (string) -> void) => {
            emit("one")
            emit("two")
            emit("three")
        })
        let out = s.collect()
        assert(out.length() == 3)
        assert(out[0] == "one")
        assert(out[1] == "two")
        assert(out[2] == "three")
    }
}
```

## Task.state -- Stateful Actors

`Task.state` creates a stateful actor backed by a task and channel. The actor holds mutable state, receives messages through a channel, and applies a handler function to update the state. Call `.send()` to send messages and `.close_and_join()` to close the channel and retrieve the final state:

```vole
let { Task } = import "std:task"

tests {
    test "state actor accumulates messages" {
        let counter = Task.state(0, (count: i64, msg: i64) -> i64 => {
            return count + msg
        })
        counter.send(1)
        counter.send(2)
        counter.send(3)
        let result = counter.close_and_join()
        assert(result == 6)
    }

    test "state actor with initial value" {
        let counter = Task.state(100, (count: i64, msg: i64) -> i64 => {
            return count + msg
        })
        counter.send(10)
        counter.send(20)
        let result = counter.close_and_join()
        assert(result == 130)
    }

    test "state actor with no messages returns initial" {
        let actor = Task.state(42, (s: i64, m: i64) -> i64 => {
            return s + m
        })
        let result = actor.close_and_join()
        assert(result == 42)
    }
}
```

State actors work with any `Sendable` type:

```vole
let { Task } = import "std:task"

tests {
    test "state actor with string concatenation" {
        let actor = Task.state("hello", (current: string, msg: string) -> string => {
            return current + " " + msg
        })
        actor.send("world")
        actor.send("from")
        actor.send("vole")
        let result = actor.close_and_join()
        assert(result == "hello world from vole")
    }

    test "state actor with bool toggles" {
        let actor = Task.state(false, (current: bool, msg: bool) -> bool => {
            if msg { return !current }
            return current
        })
        actor.send(true)   // false -> true
        actor.send(true)   // true -> false
        actor.send(true)   // false -> true
        let result = actor.close_and_join()
        assert(result == true)
    }

    test "state actor with f64 accumulates" {
        let actor = Task.state(0.0, (acc: f64, msg: f64) -> f64 => {
            return acc + msg
        })
        actor.send(1.5)
        actor.send(2.5)
        actor.send(3.0)
        let result = actor.close_and_join()
        assert(result == 7.0)
    }
}
```

Multiple tasks can send to the same state actor:

```vole
let { Task } = import "std:task"

tests {
    test "state actor fed by multiple tasks" {
        let counter = Task.state(0, (count: i64, msg: i64) -> i64 => {
            return count + msg
        })
        let t1 = Task.run(() -> i64 => {
            counter.send(10)
            return 0
        })
        let t2 = Task.run(() -> i64 => {
            counter.send(20)
            return 0
        })
        let t3 = Task.run(() -> i64 => {
            counter.send(30)
            return 0
        })
        _ = t1.join()
        _ = t2.join()
        _ = t3.join()
        let result = counter.close_and_join()
        assert(result == 60)
    }
}
```

## Channels

Channels are the communication primitive between tasks. They are typed and generic (`Channel<T>`).

### Creating Channels

Create a buffered channel with `Channel.buffered<T>(capacity)` or an unbuffered (rendezvous) channel with `Channel.new<T>()`:

```vole
let { Task, Channel } = import "std:task"

tests {
    test "buffered channel" {
        let ch = Channel.buffered<i64>(4)
        assert(ch.send(42))
        assert(ch.send(99))
        assert(ch.receive() == 42)
        assert(ch.receive() == 99)
    }

    test "unbuffered channel" {
        let ch = Channel.new<i64>()
        assert(!ch.is_closed())
        ch.close()
        assert(ch.is_closed())
    }
}
```

### send and receive

`send` returns `true` on success, `false` if the channel is closed. `receive` blocks until a value is available:

```vole
let { Task, Channel } = import "std:task"

tests {
    test "send returns false on closed channel" {
        let ch = Channel.buffered<i64>(4)
        ch.close()
        assert(!ch.send(42))
    }

    test "buffered channel FIFO order" {
        let ch = Channel.buffered<i64>(8)
        ch.send(1)
        ch.send(2)
        ch.send(3)
        ch.send(4)
        ch.send(5)
        assert(ch.receive() == 1)
        assert(ch.receive() == 2)
        assert(ch.receive() == 3)
        assert(ch.receive() == 4)
        assert(ch.receive() == 5)
    }
}
```

### try_receive

`try_receive` is a non-blocking receive that returns `T | Done`. When the channel is closed and empty, it returns `Done`:

```vole
let { Task, Channel } = import "std:task"

tests {
    test "try_receive drains then returns Done on close" {
        let ch = Channel.buffered<i64>(4)
        ch.send(10)
        ch.send(20)
        ch.close()
        let first = ch.try_receive()
        let second = ch.try_receive()
        let done = ch.try_receive()
        assert(first is i64)
        assert(second is i64)
        if first is i64 {
            assert(first == 10)
        }
        if second is i64 {
            assert(second == 20)
        }
        assert(done is Done)
    }
}
```

### close and is_closed

Close a channel to signal no more values will be sent. Double-close is a safe no-op:

```vole
let { Channel } = import "std:task"

tests {
    test "channel close" {
        let ch = Channel.buffered<i64>(4)
        assert(!ch.is_closed())
        ch.close()
        assert(ch.is_closed())
    }

    test "double close is no-op" {
        let ch = Channel.buffered<i64>(4)
        ch.close()
        ch.close()
        assert(ch.is_closed())
    }
}
```

### Channel Iterator

Call `.iter()` to get an iterator that drains all values from a closed channel:

```vole
let { Channel } = import "std:task"

tests {
    test "channel iter drains buffered values" {
        let ch = Channel.buffered<i64>(4)
        ch.send(10)
        ch.send(20)
        ch.send(30)
        ch.close()
        var sum = 0
        for v in ch.iter() {
            sum = sum + v
        }
        assert(sum == 60)
    }

    test "channel iter collect" {
        let ch = Channel.buffered<i64>(4)
        ch.send(1)
        ch.send(2)
        ch.send(3)
        ch.close()
        let arr = ch.iter().collect()
        assert(arr.length() == 3)
        assert(arr[0] == 1)
        assert(arr[1] == 2)
        assert(arr[2] == 3)
    }

    test "empty closed channel yields nothing" {
        let ch = Channel.buffered<i64>(4)
        ch.close()
        var count = 0
        for v in ch.iter() {
            count = count + 1
        }
        assert(count == 0)
    }
}
```

### Generic Channels

Channels work with any `Sendable` type -- `string`, `bool`, `f64`, structs, union types, and transferable classes:

```vole
let { Task, Channel } = import "std:task"

struct Job {
    id: i64,
    name: string,
}

tests {
    test "channel with strings" {
        let ch = Channel.buffered<string>(4)
        _ = ch.send("alpha")
        _ = ch.send("beta")
        ch.close()
        assert(ch.receive() == "alpha")
        assert(ch.receive() == "beta")
    }

    test "channel with f64" {
        let ch = Channel.buffered<f64>(2)
        _ = ch.send(1.25)
        _ = ch.send(3.5)
        ch.close()
        assert(ch.receive() == 1.25)
        assert(ch.receive() == 3.5)
    }

    test "channel with struct" {
        let ch = Channel.buffered<Job>(2)
        _ = ch.send(Job { id: 7, name: "build" })
        ch.close()
        let job = ch.receive()
        assert(job.id == 7)
        assert(job.name == "build")
    }

    test "channel with union type" {
        let ch = Channel.buffered<i64 | string>(2)
        _ = ch.send(41)
        _ = ch.send("x")
        ch.close()

        let first = ch.receive()
        assert(first is i64)
        if first is i64 {
            assert(first == 41)
        }

        let second = ch.receive()
        assert(second is string)
        if second is string {
            assert(second == "x")
        }
    }
}
```

### Transferable Classes

To send class instances through channels, implement the `Transferable` interface:

```vole
let { Task, Channel } = import "std:task"

class Token {
    label: string,
}

implement Transferable for Token {
    func transfer() -> Token {
        return Token { label: self.label }
    }
}

tests {
    test "channel with transferable class" {
        let ch = Channel.buffered<Token>(2)
        _ = ch.send(Token { label: "session" })
        ch.close()
        let token = ch.receive()
        assert(token.label == "session")
    }
}
```

## Select -- Multiplexing Channels

`Task.select2` and `Task.select3` wait on multiple channels simultaneously and return when the first channel has data available or the timeout expires. They return a `SelectResult<T>`:

```vole,ignore
struct SelectResult<T> {
    channel_index: i64,   // which channel (0, 1, or 2)
    value: T,             // the received value
    timed_out: bool,      // true if timeout expired
}
```

When `timed_out` is true, `value` is undefined and must not be read.

### select2

Wait on two channels. When both have data, the lowest index wins:

```vole
let { Task, Channel, SelectResult } = import "std:task"
let { Duration } = import "std:time"

tests {
    test "select2 returns first available" {
        let ch1 = Channel.buffered<i64>(4)
        let ch2 = Channel.buffered<i64>(4)
        ch2.send(42)
        let result = Task.select2(ch1, ch2, Duration.zero())
        assert(!result.timed_out)
        assert(result.channel_index == 1)
        assert(result.value == 42)
    }

    test "select2 lowest index wins when both ready" {
        let ch1 = Channel.buffered<i64>(4)
        let ch2 = Channel.buffered<i64>(4)
        ch1.send(10)
        ch2.send(20)
        let result = Task.select2(ch1, ch2, Duration.zero())
        assert(!result.timed_out)
        assert(result.channel_index == 0)
        assert(result.value == 10)
    }
}
```

### select3

Wait on three channels:

```vole
let { Task, Channel, SelectResult } = import "std:task"
let { Duration } = import "std:time"

tests {
    test "select3 returns correct index" {
        let ch1 = Channel.buffered<i64>(4)
        let ch2 = Channel.buffered<i64>(4)
        let ch3 = Channel.buffered<i64>(4)
        ch3.send(77)
        let result = Task.select3(ch1, ch2, ch3, Duration.zero())
        assert(!result.timed_out)
        assert(result.channel_index == 2)
        assert(result.value == 77)
    }

    test "select3 lowest index wins" {
        let ch1 = Channel.buffered<i64>(4)
        let ch2 = Channel.buffered<i64>(4)
        let ch3 = Channel.buffered<i64>(4)
        ch1.send(1)
        ch2.send(2)
        ch3.send(3)
        let result = Task.select3(ch1, ch2, ch3, Duration.zero())
        assert(!result.timed_out)
        assert(result.channel_index == 0)
        assert(result.value == 1)
    }
}
```

### Select with Timeout

Pass a `Duration` as the timeout. `Duration.zero()` means no timeout (block indefinitely). Use `Duration.nanos(1)` or similar for a short timeout:

```vole
let { Task, Channel, SelectResult } = import "std:task"
let { Duration } = import "std:time"

tests {
    test "select2 with timeout" {
        let ch1 = Channel.buffered<i64>(4)
        let ch2 = Channel.buffered<i64>(4)
        let t = Task.run(() -> i64 => {
            let result = Task.select2(ch1, ch2, Duration.nanos(1))
            if result.timed_out { return 1 }
            return 0
        })
        let v = t.join()
        assert(v == 1)
    }
}
```

### Select with Multiple Rounds

Consume values from channels one at a time using repeated select calls:

```vole
let { Task, Channel, SelectResult } = import "std:task"
let { Duration } = import "std:time"

tests {
    test "select2 multiple rounds" {
        let ch1 = Channel.buffered<i64>(4)
        let ch2 = Channel.buffered<i64>(4)
        ch1.send(10)
        ch2.send(20)

        // First select: ch1 wins (lowest index)
        let r1 = Task.select2(ch1, ch2, Duration.zero())
        assert(r1.channel_index == 0)
        assert(r1.value == 10)

        // Second select: only ch2 has data now
        let r2 = Task.select2(ch1, ch2, Duration.zero())
        assert(r2.channel_index == 1)
        assert(r2.value == 20)
    }
}
```

### Generic Select

Select works with typed channels beyond i64. Provide an explicit type parameter:

```vole
let { Task, Channel, SelectResult } = import "std:task"
let { Duration } = import "std:time"

tests {
    test "select2 with string channels" {
        let ch1 = Channel.buffered<string>(4)
        let ch2 = Channel.buffered<string>(4)
        ch2.send("hello")
        let result = Task.select2<string>(ch1, ch2, Duration.zero())
        assert(!result.timed_out)
        assert(result.channel_index == 1)
        assert(result.value == "hello")
    }

    test "select2 with f64 channels" {
        let ch1 = Channel.buffered<f64>(4)
        let ch2 = Channel.buffered<f64>(4)
        ch2.send(3.14)
        let result = Task.select2<f64>(ch1, ch2, Duration.zero())
        assert(!result.timed_out)
        assert(result.channel_index == 1)
        assert(result.value == 3.14)
    }
}
```

## Patterns

### Producer-Consumer

A task produces values through a channel while another task consumes them:

```vole
let { Task, Channel } = import "std:task"

tests {
    test "producer-consumer" {
        let ch = Channel.buffered<i64>(4)

        let producer = Task.run(() -> i64 => {
            var i = 1
            while i <= 100 {
                ch.send(i * i)
                i = i + 1
            }
            ch.close()
            return 100
        })

        let consumer = Task.run(() -> i64 => {
            var sum = 0
            while true {
                let r = ch.try_receive()
                if r is Done { break }
                if r is i64 {
                    sum = sum + r
                }
            }
            return sum
        })

        let count = producer.join()
        let total = consumer.join()

        assert(count == 100)
        // Sum of squares 1^2 + 2^2 + ... + 100^2 = 338350
        assert(total == 338350)
    }
}
```

### Pipeline

Chain multiple stages together using intermediate channels:

```vole
let { Task, Channel } = import "std:task"

tests {
    test "pipeline: producer -> transformer -> consumer" {
        let raw_ch = Channel.buffered<i64>(4)
        let processed_ch = Channel.buffered<i64>(4)

        let producer = Task.run(() -> i64 => {
            var i = 1
            while i <= 50 {
                raw_ch.send(i)
                i = i + 1
            }
            raw_ch.close()
            return 50
        })

        let transformer = Task.run(() -> i64 => {
            var count = 0
            while true {
                let r = raw_ch.try_receive()
                if r is Done { break }
                if r is i64 {
                    processed_ch.send(r * 2)
                    count = count + 1
                }
            }
            processed_ch.close()
            return count
        })

        let consumer = Task.run(() -> i64 => {
            var sum = 0
            while true {
                let r = processed_ch.try_receive()
                if r is Done { break }
                if r is i64 {
                    sum = sum + r
                }
            }
            return sum
        })

        let produced = producer.join()
        let transformed = transformer.join()
        let total = consumer.join()

        assert(produced == 50)
        assert(transformed == 50)
        // Sum of 2*1 + 2*2 + ... + 2*50 = 2550
        assert(total == 2550)
    }
}
```

### Fan-Out / Fan-In

Dispatch work to multiple workers and collect results:

```vole
let { Task, Channel } = import "std:task"

tests {
    test "fan-out fan-in" {
        let work_ch = Channel.buffered<i64>(8)
        let result_ch = Channel.buffered<i64>(20)

        let dispatcher = Task.run(() -> i64 => {
            var i = 1
            while i <= 20 {
                work_ch.send(i)
                i = i + 1
            }
            work_ch.close()
            return 20
        })

        let worker1 = Task.run(() -> i64 => {
            var count = 0
            while true {
                let r = work_ch.try_receive()
                if r is Done { break }
                if r is i64 {
                    result_ch.send(r * 10)
                    count = count + 1
                }
            }
            return count
        })

        let worker2 = Task.run(() -> i64 => {
            var count = 0
            while true {
                let r = work_ch.try_receive()
                if r is Done { break }
                if r is i64 {
                    result_ch.send(r * 10)
                    count = count + 1
                }
            }
            return count
        })

        _ = dispatcher.join()
        let w1 = worker1.join()
        let w2 = worker2.join()
        result_ch.close()

        assert(w1 + w2 == 20)

        var total = 0
        while true {
            let r = result_ch.try_receive()
            if r is Done { break }
            if r is i64 {
                total = total + r
            }
        }
        // Sum of 10*1 + 10*2 + ... + 10*20 = 2100
        assert(total == 2100)
    }
}
```

### Unbuffered Channel Communication

Unbuffered channels require a paired send/receive. A task must be ready to receive when another sends:

```vole
let { Task, Channel } = import "std:task"

tests {
    test "unbuffered channel with task" {
        let ch = Channel.new<string>()
        let producer = Task.run(() -> i64 => {
            _ = ch.send("pong")
            ch.close()
            return 0
        })

        let value = ch.receive()
        assert(value == "pong")
        _ = producer.join()
    }
}
```

### Task Producing Channel Values

Spawn a task to produce values and consume them from the main thread:

```vole
let { Task, Channel } = import "std:task"

tests {
    test "task produces channel value consumed by main" {
        let ch = Channel.buffered<i64>(2)
        let t = Task.run(() -> i64 => {
            ch.send(42)
            return 0
        })
        _ = t.join()
        assert(ch.receive() == 42)
    }
}
```

### Nested Tasks

Tasks can spawn sub-tasks using `Task.all`:

```vole
let { Task } = import "std:task"

tests {
    test "task spawns sub-tasks via all" {
        let t = Task.run(() -> i64 => {
            let fns: [() -> i64] = [
                () -> i64 => { return 10 },
                () -> i64 => { return 20 },
                () -> i64 => { return 30 },
            ]
            let results = Task.all(fns)
            return results[0] + results[1] + results[2]
        })
        assert(t.join() == 60)
    }
}
```

## API Reference

### Task\<T\>

| Method | Signature | Description |
|--------|-----------|-------------|
| `Task.run(fn)` | `(body: () -> T) -> Task<T>` | Spawn a task from a closure |
| `Task.all(fns)` | `(fns: [() -> T]) -> [T]` | Spawn all closures, collect results in order |
| `Task.parallel(items, fn)` | `(items: [T], transform: (T) -> T) -> [T]` | Transform each item in parallel |
| `Task.stream(producer)` | `(producer: ((T) -> void) -> void) -> Iterator<T>` | Create a streaming iterator |
| `Task.state(initial, handler)` | `(initial: T, handler: (T, T) -> T) -> StateActor<T>` | Create a stateful actor |
| `Task.select2(ch1, ch2, timeout)` | `(ch1: Channel<T>, ch2: Channel<T>, timeout: Duration) -> SelectResult<T>` | Wait on two channels |
| `Task.select3(ch1, ch2, ch3, timeout)` | `(ch1: Channel<T>, ch2: Channel<T>, ch3: Channel<T>, timeout: Duration) -> SelectResult<T>` | Wait on three channels |
| `.join()` | `() -> T` | Block until the task completes, return its result |
| `.cancel()` | `() -> void` | Request cooperative cancellation |
| `.is_done()` | `() -> bool` | Check if the task has completed |

### Channel\<T\>

| Method | Signature | Description |
|--------|-----------|-------------|
| `Channel.new()` | `() -> Channel<T>` | Create an unbuffered channel |
| `Channel.buffered(n)` | `(capacity: i64) -> Channel<T>` | Create a buffered channel |
| `.send(value)` | `(value: T) -> bool` | Send a value; returns false if closed |
| `.receive()` | `() -> T` | Blocking receive |
| `.try_receive()` | `() -> T \| Done` | Non-blocking receive; returns `Done` when closed and empty |
| `.close()` | `() -> void` | Close the channel (double-close is safe) |
| `.is_closed()` | `() -> bool` | Check if the channel is closed |
| `.iter()` | `() -> Iterator<T>` | Get an iterator that drains the channel |

### StateActor\<T\>

| Method | Signature | Description |
|--------|-----------|-------------|
| `.send(msg)` | `(msg: T) -> void` | Send a message to the actor |
| `.close_and_join()` | `() -> T` | Close the channel and return the final state |

### SelectResult\<T\>

| Field | Type | Description |
|-------|------|-------------|
| `channel_index` | `i64` | Which channel produced the value (0, 1, or 2) |
| `value` | `T` | The received value (undefined when `timed_out` is true) |
| `timed_out` | `bool` | Whether the timeout expired before any channel was ready |
