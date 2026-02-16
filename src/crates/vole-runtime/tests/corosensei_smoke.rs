//! Smoke test: verify corosensei links and basic coroutine switching works.

use corosensei::{Coroutine, CoroutineResult, Yielder};

#[test]
fn coroutine_basic_yield() {
    let mut coro = Coroutine::new(|yielder, input: i32| {
        let next = yielder.suspend(input * 2);
        let next2 = yielder.suspend(next * 3);
        next2 + 1
    });

    match coro.resume(5) {
        CoroutineResult::Yield(val) => assert_eq!(val, 10),
        CoroutineResult::Return(_) => panic!("expected yield"),
    }

    match coro.resume(4) {
        CoroutineResult::Yield(val) => assert_eq!(val, 12),
        CoroutineResult::Return(_) => panic!("expected yield"),
    }

    match coro.resume(99) {
        CoroutineResult::Yield(_) => panic!("expected return"),
        CoroutineResult::Return(val) => assert_eq!(val, 100),
    }
}

#[test]
fn coroutine_immediate_return() {
    let mut coro = Coroutine::new(|_yielder: &Yielder<i32, i32>, input: i32| input + 42);

    match coro.resume(0) {
        CoroutineResult::Yield(_) => panic!("expected immediate return"),
        CoroutineResult::Return(val) => assert_eq!(val, 42),
    }
}
