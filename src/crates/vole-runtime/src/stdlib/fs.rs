// src/runtime/stdlib/fs.rs
//! Native filesystem functions for std:fs/sync module.
//!
//! Fallible operations return `#[repr(C)]` structs with an error code and optional value.
//! Error codes: 0 = Ok, 1 = NotFound, 2 = PermissionDenied, 3 = IsDirectory,
//! 4 = NotDirectory, 5 = AlreadyExists, 6 = Other
//!
//! The Vole wrapper functions in stdlib/fs/sync.vole translate these error codes
//! into proper fallible(T, IoError) values.

use crate::native_registry::{NativeModule, NativeSignature, NativeType};
use crate::string::RcString;
use std::fs;
use std::io::ErrorKind;
use std::path::Path;

// =============================================================================
// C-ABI result structs
// =============================================================================

/// Result struct for operations that return a string value (read_string).
/// Fields: error (i64), value (i64 = string pointer)
/// 2 fields => returned in registers (RAX + RDX).
#[repr(C)]
pub struct ReadStringResult {
    pub code: i64,
    pub value: i64, // *const RcString as i64, only valid when error == 0
}

/// Result struct for operations that return no value (write, append, mkdir, remove).
/// Fields: error (i64)
/// 1 field => returned in 1 register (padded to 2).
#[repr(C)]
pub struct WriteResult {
    pub code: i64,
}

/// Result struct for operations that return an array value (list).
/// Fields: error (i64), value (i64 = array pointer)
/// 2 fields => returned in registers (RAX + RDX).
#[repr(C)]
pub struct ListResult {
    pub code: i64,
    pub value: i64, // *mut RcArray as i64, only valid when error == 0
}

// =============================================================================
// Error code mapping
// =============================================================================

/// Map std::io::Error to our numeric error code.
/// These codes are matched in the Vole wrapper functions in sync.vole.
fn error_to_code(err: &std::io::Error) -> i64 {
    match err.kind() {
        ErrorKind::NotFound => 1,
        ErrorKind::PermissionDenied => 2,
        ErrorKind::IsADirectory => 3,
        ErrorKind::NotADirectory => 4,
        ErrorKind::AlreadyExists => 5,
        _ => 6,
    }
}

// =============================================================================
// Module registration
// =============================================================================

/// Create the std:fs/sync native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // _read_string: (string) -> ReadStringResult { error, value }
    m.register(
        "_read_string",
        fs_read_string as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Struct { field_count: 2 },
        },
    );

    // _write_string: (string, string) -> WriteResult { error }
    m.register(
        "_write_string",
        fs_write_string as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::String],
            return_type: NativeType::Struct { field_count: 1 },
        },
    );

    // _append_string: (string, string) -> WriteResult { error }
    m.register(
        "_append_string",
        fs_append_string as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::String],
            return_type: NativeType::Struct { field_count: 1 },
        },
    );

    // _list: (string) -> ListResult { error, value }
    m.register(
        "_list",
        fs_list as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Struct { field_count: 2 },
        },
    );

    // _mkdir: (string) -> WriteResult { error }
    m.register(
        "_mkdir",
        fs_mkdir as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Struct { field_count: 1 },
        },
    );

    // exists: (string) -> bool (non-fallible, unchanged)
    m.register(
        "exists",
        fs_exists as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Bool,
        },
    );

    // is_dir: (string) -> bool (non-fallible, unchanged)
    m.register(
        "is_dir",
        fs_is_dir as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Bool,
        },
    );

    // is_file: (string) -> bool (non-fallible, unchanged)
    m.register(
        "is_file",
        fs_is_file as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Bool,
        },
    );

    // _remove_file: (string) -> WriteResult { error }
    m.register(
        "_remove_file",
        fs_remove_file as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Struct { field_count: 1 },
        },
    );

    // _remove_dir: (string) -> WriteResult { error }
    m.register(
        "_remove_dir",
        fs_remove_dir as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Struct { field_count: 1 },
        },
    );

    m
}

// =============================================================================
// Native function implementations
// =============================================================================

/// Read a file to string.
/// Returns ReadStringResult { error, value }.
#[unsafe(no_mangle)]
pub extern "C" fn fs_read_string(path_ptr: *const RcString) -> ReadStringResult {
    if path_ptr.is_null() {
        return ReadStringResult { code: 1, value: 0 };
    }

    let path_str = unsafe { (*path_ptr).as_str() };
    let path = Path::new(path_str);

    match fs::read_to_string(path) {
        Ok(contents) => {
            let s = RcString::new(&contents);
            ReadStringResult {
                code: 0,
                value: s as i64,
            }
        }
        Err(err) => ReadStringResult {
            code: error_to_code(&err),
            value: 0,
        },
    }
}

/// Write string to file (create/truncate).
/// Returns WriteResult { error }.
#[unsafe(no_mangle)]
pub extern "C" fn fs_write_string(
    path_ptr: *const RcString,
    content_ptr: *const RcString,
) -> WriteResult {
    if path_ptr.is_null() {
        return WriteResult { code: 1 };
    }

    let path_str = unsafe { (*path_ptr).as_str() };
    let content = if content_ptr.is_null() {
        ""
    } else {
        unsafe { (*content_ptr).as_str() }
    };

    match fs::write(path_str, content) {
        Ok(()) => WriteResult { code: 0 },
        Err(err) => WriteResult {
            code: error_to_code(&err),
        },
    }
}

/// Append string to file.
/// Returns WriteResult { error }.
#[unsafe(no_mangle)]
pub extern "C" fn fs_append_string(
    path_ptr: *const RcString,
    content_ptr: *const RcString,
) -> WriteResult {
    use std::fs::OpenOptions;
    use std::io::Write;

    if path_ptr.is_null() {
        return WriteResult { code: 1 };
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
        Ok(()) => WriteResult { code: 0 },
        Err(err) => WriteResult {
            code: error_to_code(&err),
        },
    }
}

/// List directory contents.
/// Returns ListResult { error, value }.
#[unsafe(no_mangle)]
pub extern "C" fn fs_list(path_ptr: *const RcString) -> ListResult {
    use crate::array::RcArray;
    use crate::value::{RuntimeTypeId, TaggedValue};

    if path_ptr.is_null() {
        return ListResult { code: 1, value: 0 };
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
                                tag: RuntimeTypeId::String as u64,
                                value: s as u64,
                            },
                        );
                    }
                }
            }
            ListResult {
                code: 0,
                value: arr as i64,
            }
        }
        Err(err) => ListResult {
            code: error_to_code(&err),
            value: 0,
        },
    }
}

/// Create a directory (and parents).
/// Returns WriteResult { error }.
#[unsafe(no_mangle)]
pub extern "C" fn fs_mkdir(path_ptr: *const RcString) -> WriteResult {
    if path_ptr.is_null() {
        return WriteResult { code: 1 };
    }

    let path_str = unsafe { (*path_ptr).as_str() };

    match fs::create_dir_all(path_str) {
        Ok(()) => WriteResult { code: 0 },
        Err(err) => WriteResult {
            code: error_to_code(&err),
        },
    }
}

/// Check if path exists.
#[unsafe(no_mangle)]
pub extern "C" fn fs_exists(path_ptr: *const RcString) -> bool {
    if path_ptr.is_null() {
        return false;
    }
    let path_str = unsafe { (*path_ptr).as_str() };
    Path::new(path_str).exists()
}

/// Check if path is a directory.
#[unsafe(no_mangle)]
pub extern "C" fn fs_is_dir(path_ptr: *const RcString) -> bool {
    if path_ptr.is_null() {
        return false;
    }
    let path_str = unsafe { (*path_ptr).as_str() };
    Path::new(path_str).is_dir()
}

/// Check if path is a file.
#[unsafe(no_mangle)]
pub extern "C" fn fs_is_file(path_ptr: *const RcString) -> bool {
    if path_ptr.is_null() {
        return false;
    }
    let path_str = unsafe { (*path_ptr).as_str() };
    Path::new(path_str).is_file()
}

/// Remove a file.
/// Returns WriteResult { error }.
#[unsafe(no_mangle)]
pub extern "C" fn fs_remove_file(path_ptr: *const RcString) -> WriteResult {
    if path_ptr.is_null() {
        return WriteResult { code: 1 };
    }

    let path_str = unsafe { (*path_ptr).as_str() };

    match fs::remove_file(path_str) {
        Ok(()) => WriteResult { code: 0 },
        Err(err) => WriteResult {
            code: error_to_code(&err),
        },
    }
}

/// Remove an empty directory.
/// Returns WriteResult { error }.
#[unsafe(no_mangle)]
pub extern "C" fn fs_remove_dir(path_ptr: *const RcString) -> WriteResult {
    if path_ptr.is_null() {
        return WriteResult { code: 1 };
    }

    let path_str = unsafe { (*path_ptr).as_str() };

    match fs::remove_dir(path_str) {
        Ok(()) => WriteResult { code: 0 },
        Err(err) => WriteResult {
            code: error_to_code(&err),
        },
    }
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

        assert_eq!(result.code, 0);
        let content = result.value as *const RcString;
        unsafe {
            assert_eq!((*content).as_str(), "hello world");
        }
    }

    #[test]
    fn test_fs_read_string_not_found() {
        let path = RcString::new("/nonexistent/file/12345.txt");
        let result = fs_read_string(path);

        assert_eq!(result.code, 1); // NotFound
    }

    #[test]
    fn test_fs_write_string_success() {
        let dir = TempDir::new().unwrap();
        let file_path = dir.path().join("test.txt");

        let path = RcString::new(file_path.to_str().unwrap());
        let content = RcString::new("test content");
        let result = fs_write_string(path, content);

        assert_eq!(result.code, 0);

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
        assert_eq!(result1.code, 0);

        // Append more content
        let path2 = RcString::new(file_path.to_str().unwrap());
        let content2 = RcString::new(" world");
        let result2 = fs_append_string(path2, content2);
        assert_eq!(result2.code, 0);

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

        assert_eq!(result.code, 0);
        unsafe {
            let arr = result.value as *mut RcArray;
            let len = RcArray::len(arr);
            assert_eq!(len, 3);
        }
    }

    #[test]
    fn test_fs_list_not_found() {
        let path = RcString::new("/nonexistent/dir/12345");
        let result = fs_list(path);

        assert_eq!(result.code, 1); // NotFound
    }

    #[test]
    fn test_fs_mkdir_success() {
        let dir = TempDir::new().unwrap();
        let new_dir = dir.path().join("new_subdir/nested");

        let path = RcString::new(new_dir.to_str().unwrap());
        let result = fs_mkdir(path);

        assert_eq!(result.code, 0);

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

        assert_eq!(result.code, 0);

        assert!(!file_path.exists());
    }

    #[test]
    fn test_fs_remove_file_not_found() {
        let path = RcString::new("/nonexistent/file/12345.txt");
        let result = fs_remove_file(path);

        assert_eq!(result.code, 1); // NotFound
    }

    #[test]
    fn test_fs_remove_dir_success() {
        let dir = TempDir::new().unwrap();
        let subdir = dir.path().join("subdir");
        fs::create_dir(&subdir).unwrap();

        let path = RcString::new(subdir.to_str().unwrap());
        let result = fs_remove_dir(path);

        assert_eq!(result.code, 0);

        assert!(!subdir.exists());
    }

    #[test]
    fn test_module_registration() {
        let m = module();

        // Check all functions are registered with underscore-prefixed names
        assert!(m.get("_read_string").is_some());
        assert!(m.get("_write_string").is_some());
        assert!(m.get("_append_string").is_some());
        assert!(m.get("_list").is_some());
        assert!(m.get("_mkdir").is_some());
        assert!(m.get("exists").is_some());
        assert!(m.get("is_dir").is_some());
        assert!(m.get("is_file").is_some());
        assert!(m.get("_remove_file").is_some());
        assert!(m.get("_remove_dir").is_some());
    }

    #[test]
    fn test_struct_return_signatures() {
        let m = module();

        // Verify struct return types
        let read = m.get("_read_string").unwrap();
        assert_eq!(
            read.signature.return_type,
            NativeType::Struct { field_count: 2 }
        );

        let write = m.get("_write_string").unwrap();
        assert_eq!(
            write.signature.return_type,
            NativeType::Struct { field_count: 1 }
        );

        let list = m.get("_list").unwrap();
        assert_eq!(
            list.signature.return_type,
            NativeType::Struct { field_count: 2 }
        );

        let mkdir = m.get("_mkdir").unwrap();
        assert_eq!(
            mkdir.signature.return_type,
            NativeType::Struct { field_count: 1 }
        );
    }
}
