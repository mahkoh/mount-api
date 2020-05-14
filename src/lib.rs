extern crate libc as upstream_libc;

use crate::libc::{
    c_int, c_uint, c_void, FSCONFIG_CMD_CREATE, FSCONFIG_CMD_RECONFIGURE,
    FSCONFIG_SET_BINARY, FSCONFIG_SET_FD, FSCONFIG_SET_FLAG, FSCONFIG_SET_PATH,
    FSCONFIG_SET_PATH_EMPTY, FSCONFIG_SET_STRING,
};
use bitflags::bitflags;
use nix::{errno::Errno, unistd::close, Error, NixPath, Result};
use std::{
    convert::TryFrom,
    ffi::CStr,
    mem,
    os::unix::io::{AsRawFd, FromRawFd, IntoRawFd, RawFd},
    ptr,
};

// copied from nix
macro_rules! libc_bitflags {
    (
        $(#[$outer:meta])*
        pub struct $BitFlags:ident: $T:ty {
            $(
                $(#[$inner:ident $($args:tt)*])*
                $Flag:ident $(as $cast:ty)*;
            )+
        }
    ) => {
        bitflags! {
            $(#[$outer])*
            pub struct $BitFlags: $T {
                $(
                    $(#[$inner $($args)*])*
                    const $Flag = libc::$Flag $(as $cast)*;
                )+
            }
        }
    };
}

mod libc {
    #![allow(non_upper_case_globals)]

    pub use upstream_libc::*;

    // https://github.com/rust-lang/libc/pull/1759
    pub const SYS_open_tree: c_long = 428;
    pub const SYS_move_mount: c_long = 429;
    pub const SYS_fsopen: c_long = 430;
    pub const SYS_fsconfig: c_long = 431;
    pub const SYS_fsmount: c_long = 432;
    pub const SYS_fspick: c_long = 433;

    // https://github.com/rust-lang/libc/pull/????
    pub const OPEN_TREE_CLONE: c_uint = 1;
    pub const OPEN_TREE_CLOEXEC: c_uint = O_CLOEXEC as c_uint;

    pub const MOVE_MOUNT_F_SYMLINKS: c_uint = 0x00000001;
    pub const MOVE_MOUNT_F_AUTOMOUNTS: c_uint = 0x00000002;
    pub const MOVE_MOUNT_F_EMPTY_PATH: c_uint = 0x00000004;
    pub const MOVE_MOUNT_T_SYMLINKS: c_uint = 0x00000010;
    pub const MOVE_MOUNT_T_AUTOMOUNTS: c_uint = 0x00000020;
    pub const MOVE_MOUNT_T_EMPTY_PATH: c_uint = 0x00000040;
    #[allow(dead_code)]
    pub const MOVE_MOUNT__MASK: c_uint = 0x00000077;

    pub const FSOPEN_CLOEXEC: c_uint = 0x00000001;

    pub const FSPICK_CLOEXEC: c_uint = 0x00000001;
    pub const FSPICK_SYMLINK_NOFOLLOW: c_uint = 0x00000002;
    pub const FSPICK_NO_AUTOMOUNT: c_uint = 0x00000004;
    pub const FSPICK_EMPTY_PATH: c_uint = 0x00000008;

    pub const FSCONFIG_SET_FLAG: c_uint = 0;
    pub const FSCONFIG_SET_STRING: c_uint = 1;
    pub const FSCONFIG_SET_BINARY: c_uint = 2;
    pub const FSCONFIG_SET_PATH: c_uint = 3;
    pub const FSCONFIG_SET_PATH_EMPTY: c_uint = 4;
    pub const FSCONFIG_SET_FD: c_uint = 5;
    pub const FSCONFIG_CMD_CREATE: c_uint = 6;
    pub const FSCONFIG_CMD_RECONFIGURE: c_uint = 7;

    pub const FSMOUNT_CLOEXEC: c_uint = 0x00000001;

    pub const MOUNT_ATTR_RDONLY: c_uint = 0x00000001;
    pub const MOUNT_ATTR_NOSUID: c_uint = 0x00000002;
    pub const MOUNT_ATTR_NODEV: c_uint = 0x00000004;
    pub const MOUNT_ATTR_NOEXEC: c_uint = 0x00000008;
    #[allow(dead_code)]
    pub const MOUNT_ATTR__ATIME: c_uint = 0x00000070;
    pub const MOUNT_ATTR_RELATIME: c_uint = 0x00000000;
    pub const MOUNT_ATTR_NOATIME: c_uint = 0x00000010;
    pub const MOUNT_ATTR_STRICTATIME: c_uint = 0x00000020;
    pub const MOUNT_ATTR_NODIRATIME: c_uint = 0x00000080;

    pub const AT_RECURSIVE: c_uint = 0x8000;
}

mod sys {
    use crate::libc::{
        c_char, c_int, c_uint, c_void, syscall, SYS_fsconfig, SYS_fsmount, SYS_fsopen,
        SYS_fspick, SYS_move_mount, SYS_open_tree,
    };

    pub unsafe fn open_tree(dfd: c_int, filename: *const c_char, flags: c_uint) -> c_int {
        syscall(SYS_open_tree, dfd, filename, flags) as c_int
    }

    pub unsafe fn move_mount(
        from_dfd: c_int,
        from_pathname: *const c_char,
        to_dfd: c_int,
        to_pathname: *const c_char,
        flags: c_uint,
    ) -> c_int {
        syscall(
            SYS_move_mount,
            from_dfd,
            from_pathname,
            to_dfd,
            to_pathname,
            flags,
        ) as c_int
    }

    pub unsafe fn fsopen(fs_name: *const c_char, flags: c_uint) -> c_int {
        syscall(SYS_fsopen, fs_name, flags) as c_int
    }

    pub unsafe fn fsconfig(
        fd: c_int,
        cmd: c_uint,
        key: *const c_char,
        value: *const c_void,
        aux: c_int,
    ) -> c_int {
        syscall(SYS_fsconfig, fd, cmd, key, value, aux) as c_int
    }

    pub unsafe fn fsmount(fs_fd: c_int, flags: c_uint, attr_flags: c_uint) -> c_int {
        syscall(SYS_fsmount, fs_fd, flags, attr_flags) as c_int
    }

    pub unsafe fn fspick(dfd: c_int, path: *const c_char, flags: c_uint) -> c_int {
        syscall(SYS_fspick, dfd, path, flags) as c_int
    }
}

libc_bitflags! {
    pub struct OpenTreeFlags: c_uint {
        AT_EMPTY_PATH as c_uint;
        AT_NO_AUTOMOUNT as c_uint;
        AT_RECURSIVE;
        AT_SYMLINK_NOFOLLOW as c_uint;
        OPEN_TREE_CLONE;
        OPEN_TREE_CLOEXEC;
    }
}

libc_bitflags! {
    pub struct MoveMountFlags: c_uint {
        MOVE_MOUNT_F_SYMLINKS;
        MOVE_MOUNT_F_AUTOMOUNTS;
        MOVE_MOUNT_F_EMPTY_PATH;
        MOVE_MOUNT_T_SYMLINKS;
        MOVE_MOUNT_T_AUTOMOUNTS;
        MOVE_MOUNT_T_EMPTY_PATH;
    }
}

libc_bitflags! {
    pub struct FsopenFlags: c_uint {
        FSOPEN_CLOEXEC;
    }
}

libc_bitflags! {
    pub struct FsmountFlags: c_uint {
        FSMOUNT_CLOEXEC;
    }
}

libc_bitflags! {
    pub struct MountAttrFlags: c_uint {
        MOUNT_ATTR_RDONLY;
        MOUNT_ATTR_NOSUID;
        MOUNT_ATTR_NODEV;
        MOUNT_ATTR_NOEXEC;
        MOUNT_ATTR_RELATIME;
        MOUNT_ATTR_NOATIME;
        MOUNT_ATTR_STRICTATIME;
        MOUNT_ATTR_NODIRATIME;
    }
}

libc_bitflags! {
    pub struct FspickFlags: c_uint {
        FSPICK_CLOEXEC;
        FSPICK_SYMLINK_NOFOLLOW;
        FSPICK_NO_AUTOMOUNT;
        FSPICK_EMPTY_PATH;
    }
}

pub fn open_tree<P>(dfd: RawFd, filename: &P, flags: OpenTreeFlags) -> Result<RawFd>
where
    P: ?Sized + NixPath,
{
    let res = filename.with_nix_path(|filename| unsafe {
        sys::open_tree(dfd, filename.as_ptr(), flags.bits())
    })?;
    Errno::result(res)
}

pub fn move_mount<P, Q>(
    from_dfd: RawFd,
    from_pathname: &P,
    to_dfd: RawFd,
    to_pathname: &Q,
    flags: MoveMountFlags,
) -> Result<()>
where
    P: ?Sized + NixPath,
    Q: ?Sized + NixPath,
{
    let res = from_pathname.with_nix_path(|from_pathname| {
        to_pathname.with_nix_path(|to_pathname| unsafe {
            sys::move_mount(
                from_dfd,
                from_pathname.as_ptr(),
                to_dfd,
                to_pathname.as_ptr(),
                flags.bits(),
            )
        })
    })??;
    Errno::result(res).map(drop)
}

pub fn fsopen(fs_name: &CStr, flags: FsopenFlags) -> Result<RawFd> {
    let res = unsafe { sys::fsopen(fs_name.as_ptr(), flags.bits()) };
    Errno::result(res)
}

pub fn fsconfig_set_flag(fs_fd: RawFd, key: &CStr) -> Result<()> {
    let res =
        unsafe { sys::fsconfig(fs_fd, FSCONFIG_SET_FLAG, key.as_ptr(), ptr::null(), 0) };
    Errno::result(res).map(drop)
}

pub fn fsconfig_set_string(fs_fd: RawFd, key: &CStr, value: &CStr) -> Result<()> {
    let res = unsafe {
        sys::fsconfig(
            fs_fd,
            FSCONFIG_SET_STRING,
            key.as_ptr(),
            value.as_ptr() as *const c_void,
            0,
        )
    };
    Errno::result(res).map(drop)
}

pub fn fsconfig_set_binary(fs_fd: RawFd, key: &CStr, value: &[u8]) -> Result<()> {
    let len = match c_int::try_from(value.len()) {
        Ok(len) => len,
        Err(_) => return Err(Error::Sys(Errno::EINVAL)),
    };
    let res = unsafe {
        sys::fsconfig(
            fs_fd,
            FSCONFIG_SET_BINARY,
            key.as_ptr(),
            value.as_ptr() as *const c_void,
            len,
        )
    };
    Errno::result(res).map(drop)
}

fn _fsconfig_set_path<P>(
    fs_fd: RawFd,
    cmd: c_uint,
    key: &CStr,
    dfd: RawFd,
    path: &P,
) -> Result<()>
where
    P: ?Sized + NixPath,
{
    let res = path.with_nix_path(|path| unsafe {
        sys::fsconfig(
            fs_fd,
            cmd,
            key.as_ptr(),
            path.as_ptr() as *const c_void,
            dfd,
        )
    })?;
    Errno::result(res).map(drop)
}

pub fn fsconfig_set_path<P>(fs_fd: RawFd, key: &CStr, dfd: RawFd, path: &P) -> Result<()>
where
    P: ?Sized + NixPath,
{
    _fsconfig_set_path(fs_fd, FSCONFIG_SET_PATH, key, dfd, path)
}

pub fn fsconfig_set_path_empty<P>(
    fs_fd: RawFd,
    key: &CStr,
    dfd: RawFd,
    path: &P,
) -> Result<()>
where
    P: ?Sized + NixPath,
{
    _fsconfig_set_path(fs_fd, FSCONFIG_SET_PATH_EMPTY, key, dfd, path)
}

pub fn fsconfig_set_fd(fs_fd: RawFd, key: &CStr, fd: RawFd) -> Result<()> {
    let res =
        unsafe { sys::fsconfig(fs_fd, FSCONFIG_SET_FD, key.as_ptr(), ptr::null(), fd) };
    Errno::result(res).map(drop)
}

fn _fsconfig_cmd(fs_fd: RawFd, cmd: c_uint) -> Result<()> {
    let res = unsafe { sys::fsconfig(fs_fd, cmd, ptr::null(), ptr::null(), 0) };
    Errno::result(res).map(drop)
}

pub fn fsconfig_cmd_create(fs_fd: RawFd) -> Result<()> {
    _fsconfig_cmd(fs_fd, FSCONFIG_CMD_CREATE)
}

pub fn fsconfig_cmd_reconfigure(fs_fd: RawFd) -> Result<()> {
    _fsconfig_cmd(fs_fd, FSCONFIG_CMD_RECONFIGURE)
}

pub fn fsmount(
    fs_fd: RawFd,
    flags: FsmountFlags,
    attr_flags: MountAttrFlags,
) -> Result<RawFd> {
    let res = unsafe { sys::fsmount(fs_fd, flags.bits(), attr_flags.bits()) };
    Errno::result(res)
}

pub fn fspick<P>(dfd: RawFd, path: &P, flags: FspickFlags) -> Result<RawFd>
where
    P: ?Sized + NixPath,
{
    let res = path
        .with_nix_path(|path| unsafe { sys::fspick(dfd, path.as_ptr(), flags.bits()) })?;
    Errno::result(res)
}

pub struct Mount {
    mnt_fd: RawFd,
}

impl Mount {
    pub fn move_mount<P>(
        &self,
        to_dfd: RawFd,
        to_path: &P,
        mut flags: MoveMountFlags,
    ) -> Result<()>
    where
        P: ?Sized + NixPath,
    {
        flags |= MoveMountFlags::MOVE_MOUNT_F_EMPTY_PATH;
        move_mount(
            self.mnt_fd,
            CStr::from_bytes_with_nul(b"\0").unwrap(),
            to_dfd,
            to_path,
            flags,
        )
    }

    pub fn open<P>(dfd: RawFd, path: &P, flags: OpenTreeFlags) -> Result<Self>
    where
        P: ?Sized + NixPath,
    {
        Ok(Mount {
            mnt_fd: open_tree(dfd, path, flags)?,
        })
    }
}

impl Drop for Mount {
    fn drop(&mut self) {
        let _ = close(self.mnt_fd);
    }
}

impl AsRawFd for Mount {
    fn as_raw_fd(&self) -> RawFd {
        self.mnt_fd
    }
}

impl IntoRawFd for Mount {
    fn into_raw_fd(self) -> RawFd {
        let mnt_fd = self.mnt_fd;
        mem::forget(self);
        mnt_fd
    }
}

impl FromRawFd for Mount {
    unsafe fn from_raw_fd(mnt_fd: RawFd) -> Self {
        Mount { mnt_fd }
    }
}

pub struct Fs {
    fs_fd: RawFd,
}

impl Fs {
    pub fn open(fs_name: &CStr, flags: FsopenFlags) -> Result<Self> {
        Ok(Fs {
            fs_fd: fsopen(fs_name, flags)?,
        })
    }

    pub fn pick<P>(dfd: RawFd, path: &P, flags: FspickFlags) -> Result<Self>
    where
        P: ?Sized + NixPath,
    {
        Ok(Fs {
            fs_fd: fspick(dfd, path, flags)?,
        })
    }

    pub fn set_flag(&self, key: &CStr) -> Result<()> {
        fsconfig_set_flag(self.fs_fd, key)
    }

    pub fn set_string(&self, key: &CStr, value: &CStr) -> Result<()> {
        fsconfig_set_string(self.fs_fd, key, value)
    }

    pub fn set_binary(&self, key: &CStr, value: &[u8]) -> Result<()> {
        fsconfig_set_binary(self.fs_fd, key, value)
    }

    pub fn set_path<P>(&self, key: &CStr, dfd: RawFd, path: &P) -> Result<()>
    where
        P: ?Sized + NixPath,
    {
        fsconfig_set_path(self.fs_fd, key, dfd, path)
    }

    pub fn set_path_empty<P>(&self, key: &CStr, dfd: RawFd, path: &P) -> Result<()>
    where
        P: ?Sized + NixPath,
    {
        fsconfig_set_path_empty(self.fs_fd, key, dfd, path)
    }

    pub fn set_path_fd(&self, key: &CStr, fd: RawFd) -> Result<()> {
        fsconfig_set_fd(self.fs_fd, key, fd)
    }

    pub fn create(&self) -> Result<()> {
        fsconfig_cmd_create(self.fs_fd)
    }

    pub fn reconfigure(&self) -> Result<()> {
        fsconfig_cmd_reconfigure(self.fs_fd)
    }

    pub fn mount(
        &self,
        flags: FsmountFlags,
        attr_flags: MountAttrFlags,
    ) -> Result<Mount> {
        Ok(Mount {
            mnt_fd: fsmount(self.fs_fd, flags, attr_flags)?,
        })
    }
}

impl Drop for Fs {
    fn drop(&mut self) {
        let _ = close(self.fs_fd);
    }
}

impl AsRawFd for Fs {
    fn as_raw_fd(&self) -> RawFd {
        self.fs_fd
    }
}

impl IntoRawFd for Fs {
    fn into_raw_fd(self) -> RawFd {
        let fs_fd = self.fs_fd;
        mem::forget(self);
        fs_fd
    }
}

impl FromRawFd for Fs {
    unsafe fn from_raw_fd(fs_fd: RawFd) -> Self {
        Fs { fs_fd }
    }
}

#[cfg(test)]
mod test {
    use crate::*;
    use nix::{
        fcntl::{openat, OFlag},
        libc::AT_FDCWD,
        mount::{mount, umount2, MntFlags, MsFlags},
        sys::stat::Mode,
        unistd::close,
        NixPath,
    };
    use std::{
        ffi::CStr,
        fs,
        os::unix::io::{AsRawFd, RawFd},
        path::Path,
    };
    use tempfile::{tempdir, tempdir_in};

    fn cstr(s: &str) -> &CStr {
        CStr::from_bytes_with_nul(s.as_bytes()).unwrap()
    }

    fn tmpfs() -> Mount {
        let fs = Fs::open(cstr("tmpfs\0"), FsopenFlags::empty()).unwrap();
        fs.create().unwrap();
        fs.mount(FsmountFlags::empty(), MountAttrFlags::empty())
            .unwrap()
    }

    fn with_mount_point<'a, P: Into<Option<&'a Path>>, T, F: FnOnce(&Path) -> T>(
        base: P,
        f: F,
    ) -> T {
        struct Umount<'a>(&'a Path);

        impl<'a> Drop for Umount<'a> {
            fn drop(&mut self) {
                let _ = umount2(self.0, MntFlags::MNT_DETACH);
            }
        }

        let dir = match base.into() {
            Some(base) => tempdir_in(base),
            _ => tempdir(),
        }
        .unwrap();
        let _umount = Umount(dir.path());
        f(dir.path())
    }

    fn with_private_mount<T, F: FnOnce(&Path) -> T>(f: F) -> T {
        with_mount_point(None, |path| {
            let fs = tmpfs();
            fs.move_mount(AT_FDCWD, path, MoveMountFlags::empty())
                .unwrap();
            mount::<Path, _, Path, Path>(None, path, None, MsFlags::MS_PRIVATE, None)
                .unwrap();
            f(path)
        })
    }

    fn create_file<P: ?Sized + NixPath>(dfd: RawFd, p: &P) {
        let _ = close(
            openat(dfd, p, OFlag::O_CREAT | OFlag::O_RDONLY, Mode::empty()).unwrap(),
        );
    }

    #[test]
    fn move_mount1() {
        with_private_mount(|path| {
            with_mount_point(path, |p1| {
                with_mount_point(path, |p2| {
                    const FILE: &str = "test";

                    let mnt = tmpfs();
                    create_file(mnt.as_raw_fd(), FILE);

                    // move to p1
                    mnt.move_mount(AT_FDCWD, p1, MoveMountFlags::empty())
                        .unwrap();
                    assert!(p1.join(FILE).exists());

                    // move from p1 to p2
                    mnt.move_mount(AT_FDCWD, p2, MoveMountFlags::empty())
                        .unwrap();
                    assert!(!p1.join(FILE).exists());
                    assert!(p2.join(FILE).exists());

                    // open tree at p2 and move to p1
                    let mnt = Mount::open(AT_FDCWD, p2, OpenTreeFlags::empty()).unwrap();
                    mnt.move_mount(AT_FDCWD, p1, MoveMountFlags::empty())
                        .unwrap();
                    assert!(p1.join(FILE).exists());
                    assert!(!p2.join(FILE).exists());

                    // move from p2 to p1
                    move_mount(AT_FDCWD, p1, AT_FDCWD, p2, MoveMountFlags::empty())
                        .unwrap();
                    assert!(!p1.join(FILE).exists());
                    assert!(p2.join(FILE).exists());

                    // clone tree at p2 and attach to p1
                    let mnt = Mount::open(AT_FDCWD, p2, OpenTreeFlags::OPEN_TREE_CLONE)
                        .unwrap();
                    mnt.move_mount(AT_FDCWD, p1, MoveMountFlags::empty())
                        .unwrap();
                    assert!(p1.join(FILE).exists());
                    assert!(p2.join(FILE).exists());
                });
            });
        });
    }

    #[test]
    fn fspick1() {
        with_mount_point(None, |p1| {
            let mnt = tmpfs();
            mnt.move_mount(AT_FDCWD, p1, MoveMountFlags::empty())
                .unwrap();

            fs::create_dir(p1.join("a")).unwrap();

            // make read-only
            let fs = Fs::pick(AT_FDCWD, p1, FspickFlags::empty()).unwrap();
            fs.set_flag(CStr::from_bytes_with_nul(b"ro\0").unwrap())
                .unwrap();
            fs.reconfigure().unwrap();

            assert!(fs::create_dir(p1.join("b")).is_err());
        });
    }

    #[test]
    fn fsmount1() {
        let fs = Fs::open(cstr("proc\0"), FsopenFlags::empty()).unwrap();
        fs.create().unwrap();
        let mnt = fs
            .mount(FsmountFlags::empty(), MountAttrFlags::empty())
            .unwrap();

        // open /proc/cpuinfo
        let _ = close(
            openat(mnt.as_raw_fd(), "cpuinfo", OFlag::O_RDONLY, Mode::empty()).unwrap(),
        );
    }
}
