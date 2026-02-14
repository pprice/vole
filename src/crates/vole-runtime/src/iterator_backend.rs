//! Backend selection and adapter controls for iterator runtime.

use std::sync::atomic::{AtomicU8, Ordering};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum IteratorBackend {
    Legacy = 0,
    NewCore = 1,
}

static BACKEND_OVERRIDE: AtomicU8 = AtomicU8::new(u8::MAX);

pub(crate) fn active_backend() -> IteratorBackend {
    match BACKEND_OVERRIDE.load(Ordering::Relaxed) {
        x if x == IteratorBackend::Legacy as u8 => IteratorBackend::Legacy,
        x if x == IteratorBackend::NewCore as u8 => IteratorBackend::NewCore,
        _ => default_backend(),
    }
}

fn default_backend() -> IteratorBackend {
    #[cfg(test)]
    {
        match std::env::var("VOLE_ITERATOR_RUNTIME_BACKEND")
            .ok()
            .as_deref()
        {
            Some("new_core") => IteratorBackend::NewCore,
            _ => IteratorBackend::Legacy,
        }
    }
    #[cfg(not(test))]
    {
        IteratorBackend::Legacy
    }
}

#[cfg(test)]
pub(crate) fn with_backend<T>(backend: IteratorBackend, f: impl FnOnce() -> T) -> T {
    let prev = BACKEND_OVERRIDE.swap(backend as u8, Ordering::Relaxed);
    let out = f();
    BACKEND_OVERRIDE.store(prev, Ordering::Relaxed);
    out
}
