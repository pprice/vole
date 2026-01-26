// src/runtime/stdlib/fs.rs
//! Native filesystem functions for std:fs/sync module.
//!
//! All fallible operations return a boxed fallible type:
//! - Offset 0 (i64): Tag - 0 for success, 1+ for error variant
//! - Offset 8: Payload - success value or error data (path string pointer)
//!
//! Error tags matching Vole's sorted union order for:
//!   NotFound | PermissionDenied | IsDirectory | NotDirectory | AlreadyExists | Other
//!
//! Vole sorts union types in reverse debug format order, resulting in:
//! - 0 = success
//! - 1 = Other
//! - 2 = AlreadyExists
//! - 3 = NotDirectory
//! - 4 = IsDirectory
//! - 5 = PermissionDenied
//! - 6 = NotFound

use crate::native_registry::{NativeModule, NativeSignature, NativeType};
use crate::string::RcString;
use std::alloc::{Layout, alloc};
use std::fs;
use std::io::ErrorKind;
use std::path::Path;

// Error tags matching Vole's sorted union order (reverse of declaration order)
const TAG_SUCCESS: i64 = 0;
const TAG_OTHER: i64 = 1;
const TAG_ALREADY_EXISTS: i64 = 2;
const TAG_NOT_DIRECTORY: i64 = 3;
const TAG_IS_DIRECTORY: i64 = 4;
const TAG_PERMISSION_DENIED: i64 = 5;
const TAG_NOT_FOUND: i64 = 6;

/// Create the std:fs/sync native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // read_string: (string) -> fallible(string, IoError)
    // Returns ptr to boxed fallible result
    m.register(
        "read_string",
        fs_read_string as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::I64, // Pointer to fallible
        },
    );

    // write_string: (string, string) -> fallible(bool, IoError)
    // Returns ptr to boxed fallible result (bool = Done)
    m.register(
        "write_string",
        fs_write_string as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::String],
            return_type: NativeType::I64, // Pointer to fallible
        },
    );

    // append_string: (string, string) -> fallible(bool, IoError)
    // Returns ptr to boxed fallible result (bool = Done)
    m.register(
        "append_string",
        fs_append_string as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::String],
            return_type: NativeType::I64, // Pointer to fallible
        },
    );

    // list: (string) -> fallible([string], IoError)
    // Returns ptr to boxed fallible result (array of strings)
    m.register(
        "list",
        fs_list as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::I64, // Pointer to fallible
        },
    );

    // mkdir: (string) -> fallible(bool, IoError)
    // Returns ptr to boxed fallible result (bool = Done)
    m.register(
        "mkdir",
        fs_mkdir as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::I64, // Pointer to fallible
        },
    );

    // exists: (string) -> bool
    m.register(
        "exists",
        fs_exists as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Bool,
        },
    );

    // is_dir: (string) -> bool
    m.register(
        "is_dir",
        fs_is_dir as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Bool,
        },
    );

    // is_file: (string) -> bool
    m.register(
        "is_file",
        fs_is_file as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Bool,
        },
    );

    // remove_file: (string) -> fallible(bool, IoError)
    m.register(
        "remove_file",
        fs_remove_file as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::I64, // Pointer to fallible
        },
    );

    // remove_dir: (string) -> fallible(bool, IoError)
    m.register(
        "remove_dir",
        fs_remove_dir as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::I64, // Pointer to fallible
        },
    );

    m
}

// =============================================================================
// Helper functions
// =============================================================================

/// Allocate a boxed fallible result (16 bytes: tag + payload)
fn alloc_fallible() -> *mut u8 {
    let layout = Layout::from_size_align(16, 8).expect("valid fallible layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    ptr
}

/// Map std::io::Error to our error tag
fn error_to_tag(err: &std::io::Error) -> i64 {
    match err.kind() {
        ErrorKind::NotFound => TAG_NOT_FOUND,
        ErrorKind::PermissionDenied => TAG_PERMISSION_DENIED,
        ErrorKind::IsADirectory => TAG_IS_DIRECTORY,
        ErrorKind::NotADirectory => TAG_NOT_DIRECTORY,
        ErrorKind::AlreadyExists => TAG_ALREADY_EXISTS,
        _ => TAG_OTHER,
    }
}

/// Write success with string payload
fn write_success_string(ptr: *mut u8, s: *const RcString) {
    unsafe {
        std::ptr::write(ptr as *mut i64, TAG_SUCCESS);
        std::ptr::write(ptr.add(8) as *mut i64, s as i64);
    }
}

/// Write success with Done (bool true) payload
fn write_success_done(ptr: *mut u8) {
    unsafe {
        std::ptr::write(ptr as *mut i64, TAG_SUCCESS);
        std::ptr::write(ptr.add(8) as *mut i64, 1); // Done = true
    }
}

/// Write success with array payload
fn write_success_array(ptr: *mut u8, arr: *mut crate::array::RcArray) {
    unsafe {
        std::ptr::write(ptr as *mut i64, TAG_SUCCESS);
        std::ptr::write(ptr.add(8) as *mut i64, arr as i64);
    }
}

/// Write error with path payload
fn write_error(ptr: *mut u8, tag: i64, path: *const RcString) {
    unsafe {
        std::ptr::write(ptr as *mut i64, tag);
        std::ptr::write(ptr.add(8) as *mut i64, path as i64);
    }
}

// =============================================================================
// Native function implementations
// =============================================================================

/// Read a file to string.
/// Returns a boxed fallible: success(string) or error with path.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn fs_read_string(path_ptr: *const RcString) -> *mut u8 {
    let result_ptr = alloc_fallible();

    if path_ptr.is_null() {
        let path_str = RcString::new("");
        write_error(result_ptr, TAG_NOT_FOUND, path_str);
        return result_ptr;
    }

    let path_str = unsafe { (*path_ptr).as_str() };
    let path = Path::new(path_str);

    match fs::read_to_string(path) {
        Ok(contents) => {
            let s = RcString::new(&contents);
            write_success_string(result_ptr, s);
        }
        Err(err) => {
            let tag = error_to_tag(&err);
            // Clone the path for error context
            let path_copy = RcString::new(path_str);
            write_error(result_ptr, tag, path_copy);
        }
    }

    result_ptr
}

/// Write string to file (create/truncate).
/// Returns a boxed fallible: success(Done) or error with path.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn fs_write_string(
    path_ptr: *const RcString,
    content_ptr: *const RcString,
) -> *mut u8 {
    let result_ptr = alloc_fallible();

    if path_ptr.is_null() {
        let path_str = RcString::new("");
        write_error(result_ptr, TAG_NOT_FOUND, path_str);
        return result_ptr;
    }

    let path_str = unsafe { (*path_ptr).as_str() };
    let content = if content_ptr.is_null() {
        ""
    } else {
        unsafe { (*content_ptr).as_str() }
    };

    match fs::write(path_str, content) {
        Ok(()) => {
            write_success_done(result_ptr);
        }
        Err(err) => {
            let tag = error_to_tag(&err);
            let path_copy = RcString::new(path_str);
            write_error(result_ptr, tag, path_copy);
        }
    }

    result_ptr
}

/// Append string to file.
/// Returns a boxed fallible: success(Done) or error with path.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn fs_append_string(
    path_ptr: *const RcString,
    content_ptr: *const RcString,
) -> *mut u8 {
    use std::fs::OpenOptions;
    use std::io::Write;

    let result_ptr = alloc_fallible();

    if path_ptr.is_null() {
        let path_str = RcString::new("");
        write_error(result_ptr, TAG_NOT_FOUND, path_str);
        return result_ptr;
    }

    let path_str = unsafe { (*path_ptr).as_str() };
    let content = if content_ptr.is_null() {
        ""
    } else {
        unsafe { (*content_ptr).as_str() }
    };

    let result = OpenOptions::new()
        .create(true)
        .append(true)
        .open(path_str)
        .and_then(|mut file| file.write_all(content.as_bytes()));

    match result {
        Ok(()) => {
            write_success_done(result_ptr);
        }
        Err(err) => {
            let tag = error_to_tag(&err);
            let path_copy = RcString::new(path_str);
            write_error(result_ptr, tag, path_copy);
        }
    }

    result_ptr
}

/// List directory contents.
/// Returns a boxed fallible: success([string]) or error with path.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn fs_list(path_ptr: *const RcString) -> *mut u8 {
    use crate::array::RcArray;
    use crate::value::{TYPE_STRING, TaggedValue};

    let result_ptr = alloc_fallible();

    if path_ptr.is_null() {
        let path_str = RcString::new("");
        write_error(result_ptr, TAG_NOT_FOUND, path_str);
        return result_ptr;
    }

    let path_str = unsafe { (*path_ptr).as_str() };
    let path = Path::new(path_str);

    match fs::read_dir(path) {
        Ok(entries) => {
            let arr = RcArray::with_capacity(16);
            for entry in entries.flatten() {
                if let Some(name) = entry.file_name().to_str() {
                    let s = RcString::new(name);
                    unsafe {
                        RcArray::push(
                            arr,
                            TaggedValue {
                                tag: TYPE_STRING as u64,
                                value: s as u64,
                            },
                        );
                    }
                }
            }
            write_success_array(result_ptr, arr);
        }
        Err(err) => {
            let tag = error_to_tag(&err);
            let path_copy = RcString::new(path_str);
            write_error(result_ptr, tag, path_copy);
        }
    }

    result_ptr
}

/// Create a directory (and parents).
/// Returns a boxed fallible: success(Done) or error with path.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn fs_mkdir(path_ptr: *const RcString) -> *mut u8 {
    let result_ptr = alloc_fallible();

    if path_ptr.is_null() {
        let path_str = RcString::new("");
        write_error(result_ptr, TAG_NOT_FOUND, path_str);
        return result_ptr;
    }

    let path_str = unsafe { (*path_ptr).as_str() };

    match fs::create_dir_all(path_str) {
        Ok(()) => {
            write_success_done(result_ptr);
        }
        Err(err) => {
            let tag = error_to_tag(&err);
            let path_copy = RcString::new(path_str);
            write_error(result_ptr, tag, path_copy);
        }
    }

    result_ptr
}

/// Check if path exists.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn fs_exists(path_ptr: *const RcString) -> bool {
    if path_ptr.is_null() {
        return false;
    }
    let path_str = unsafe { (*path_ptr).as_str() };
    Path::new(path_str).exists()
}

/// Check if path is a directory.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn fs_is_dir(path_ptr: *const RcString) -> bool {
    if path_ptr.is_null() {
        return false;
    }
    let path_str = unsafe { (*path_ptr).as_str() };
    Path::new(path_str).is_dir()
}

/// Check if path is a file.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn fs_is_file(path_ptr: *const RcString) -> bool {
    if path_ptr.is_null() {
        return false;
    }
    let path_str = unsafe { (*path_ptr).as_str() };
    Path::new(path_str).is_file()
}

/// Remove a file.
/// Returns a boxed fallible: success(Done) or error with path.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn fs_remove_file(path_ptr: *const RcString) -> *mut u8 {
    let result_ptr = alloc_fallible();

    if path_ptr.is_null() {
        let path_str = RcString::new("");
        write_error(result_ptr, TAG_NOT_FOUND, path_str);
        return result_ptr;
    }

    let path_str = unsafe { (*path_ptr).as_str() };

    match fs::remove_file(path_str) {
        Ok(()) => {
            write_success_done(result_ptr);
        }
        Err(err) => {
            let tag = error_to_tag(&err);
            let path_copy = RcString::new(path_str);
            write_error(result_ptr, tag, path_copy);
        }
    }

    result_ptr
}

/// Remove an empty directory.
/// Returns a boxed fallible: success(Done) or error with path.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn fs_remove_dir(path_ptr: *const RcString) -> *mut u8 {
    let result_ptr = alloc_fallible();

    if path_ptr.is_null() {
        let path_str = RcString::new("");
        write_error(result_ptr, TAG_NOT_FOUND, path_str);
        return result_ptr;
    }

    let path_str = unsafe { (*path_ptr).as_str() };

    match fs::remove_dir(path_str) {
        Ok(()) => {
            write_success_done(result_ptr);
        }
        Err(err) => {
            let tag = error_to_tag(&err);
            let path_copy = RcString::new(path_str);
            write_error(result_ptr, tag, path_copy);
        }
    }

    result_ptr
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::io::Write;
    use tempfile::TempDir;

    // Helper to read tag from fallible result
    unsafe fn read_tag(ptr: *mut u8) -> i64 {
        unsafe { std::ptr::read(ptr as *const i64) }
    }

    // Helper to read payload as string ptr from fallible result
    unsafe fn read_payload_string(ptr: *mut u8) -> *const RcString {
        unsafe { std::ptr::read(ptr.add(8) as *const i64) as *const RcString }
    }

    // Helper to read string value
    unsafe fn read_string(s: *const RcString) -> String {
        if s.is_null() {
            String::new()
        } else {
            unsafe { (*s).as_str().to_string() }
        }
    }

    #[test]
    fn test_fs_exists() {
        let dir = TempDir::new().unwrap();
        let file_path = dir.path().join("test.txt");
        File::create(&file_path).unwrap();

        let path = RcString::new(file_path.to_str().unwrap());
        assert!(fs_exists(path));

        let nonexistent = RcString::new("/nonexistent/path/12345");
        assert!(!fs_exists(nonexistent));

        assert!(!fs_exists(std::ptr::null()));
    }

    #[test]
    fn test_fs_is_dir() {
        let dir = TempDir::new().unwrap();
        let path = RcString::new(dir.path().to_str().unwrap());
        assert!(fs_is_dir(path));

        let file_path = dir.path().join("test.txt");
        File::create(&file_path).unwrap();
        let file_str = RcString::new(file_path.to_str().unwrap());
        assert!(!fs_is_dir(file_str));

        assert!(!fs_is_dir(std::ptr::null()));
    }

    #[test]
    fn test_fs_is_file() {
        let dir = TempDir::new().unwrap();
        let file_path = dir.path().join("test.txt");
        File::create(&file_path).unwrap();

        let path = RcString::new(file_path.to_str().unwrap());
        assert!(fs_is_file(path));

        let dir_path = RcString::new(dir.path().to_str().unwrap());
        assert!(!fs_is_file(dir_path));

        assert!(!fs_is_file(std::ptr::null()));
    }

    #[test]
    fn test_fs_read_string_success() {
        let dir = TempDir::new().unwrap();
        let file_path = dir.path().join("test.txt");
        let mut file = File::create(&file_path).unwrap();
        file.write_all(b"hello world").unwrap();

        let path = RcString::new(file_path.to_str().unwrap());
        let result = fs_read_string(path);

        unsafe {
            assert_eq!(read_tag(result), TAG_SUCCESS);
            let content = read_payload_string(result);
            assert_eq!(read_string(content), "hello world");
        }
    }

    #[test]
    fn test_fs_read_string_not_found() {
        let path = RcString::new("/nonexistent/file/12345.txt");
        let result = fs_read_string(path);

        unsafe {
            assert_eq!(read_tag(result), TAG_NOT_FOUND);
        }
    }

    #[test]
    fn test_fs_write_string_success() {
        let dir = TempDir::new().unwrap();
        let file_path = dir.path().join("test.txt");

        let path = RcString::new(file_path.to_str().unwrap());
        let content = RcString::new("test content");
        let result = fs_write_string(path, content);

        unsafe {
            assert_eq!(read_tag(result), TAG_SUCCESS);
        }

        // Verify file was written
        let contents = fs::read_to_string(&file_path).unwrap();
        assert_eq!(contents, "test content");
    }

    #[test]
    fn test_fs_append_string() {
        let dir = TempDir::new().unwrap();
        let file_path = dir.path().join("test.txt");

        // Write initial content
        let path1 = RcString::new(file_path.to_str().unwrap());
        let content1 = RcString::new("hello");
        let result1 = fs_write_string(path1, content1);
        unsafe {
            assert_eq!(read_tag(result1), TAG_SUCCESS);
        }

        // Append more content
        let path2 = RcString::new(file_path.to_str().unwrap());
        let content2 = RcString::new(" world");
        let result2 = fs_append_string(path2, content2);
        unsafe {
            assert_eq!(read_tag(result2), TAG_SUCCESS);
        }

        // Verify combined content
        let contents = fs::read_to_string(&file_path).unwrap();
        assert_eq!(contents, "hello world");
    }

    #[test]
    fn test_fs_list_success() {
        use crate::array::RcArray;

        let dir = TempDir::new().unwrap();
        File::create(dir.path().join("a.txt")).unwrap();
        File::create(dir.path().join("b.txt")).unwrap();
        fs::create_dir(dir.path().join("subdir")).unwrap();

        let path = RcString::new(dir.path().to_str().unwrap());
        let result = fs_list(path);

        unsafe {
            assert_eq!(read_tag(result), TAG_SUCCESS);
            let arr = std::ptr::read(result.add(8) as *const i64) as *mut RcArray;
            let len = RcArray::len(arr);
            assert_eq!(len, 3);
        }
    }

    #[test]
    fn test_fs_list_not_found() {
        let path = RcString::new("/nonexistent/dir/12345");
        let result = fs_list(path);

        unsafe {
            assert_eq!(read_tag(result), TAG_NOT_FOUND);
        }
    }

    #[test]
    fn test_fs_mkdir_success() {
        let dir = TempDir::new().unwrap();
        let new_dir = dir.path().join("new_subdir/nested");

        let path = RcString::new(new_dir.to_str().unwrap());
        let result = fs_mkdir(path);

        unsafe {
            assert_eq!(read_tag(result), TAG_SUCCESS);
        }

        assert!(new_dir.exists());
        assert!(new_dir.is_dir());
    }

    #[test]
    fn test_fs_remove_file_success() {
        let dir = TempDir::new().unwrap();
        let file_path = dir.path().join("test.txt");
        File::create(&file_path).unwrap();

        let path = RcString::new(file_path.to_str().unwrap());
        let result = fs_remove_file(path);

        unsafe {
            assert_eq!(read_tag(result), TAG_SUCCESS);
        }

        assert!(!file_path.exists());
    }

    #[test]
    fn test_fs_remove_file_not_found() {
        let path = RcString::new("/nonexistent/file/12345.txt");
        let result = fs_remove_file(path);

        unsafe {
            assert_eq!(read_tag(result), TAG_NOT_FOUND);
        }
    }

    #[test]
    fn test_fs_remove_dir_success() {
        let dir = TempDir::new().unwrap();
        let subdir = dir.path().join("subdir");
        fs::create_dir(&subdir).unwrap();

        let path = RcString::new(subdir.to_str().unwrap());
        let result = fs_remove_dir(path);

        unsafe {
            assert_eq!(read_tag(result), TAG_SUCCESS);
        }

        assert!(!subdir.exists());
    }

    #[test]
    fn test_module_registration() {
        let m = module();

        // Check all functions are registered
        assert!(m.get("read_string").is_some());
        assert!(m.get("write_string").is_some());
        assert!(m.get("append_string").is_some());
        assert!(m.get("list").is_some());
        assert!(m.get("mkdir").is_some());
        assert!(m.get("exists").is_some());
        assert!(m.get("is_dir").is_some());
        assert!(m.get("is_file").is_some());
        assert!(m.get("remove_file").is_some());
        assert!(m.get("remove_dir").is_some());
    }
}
