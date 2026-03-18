/// Represents the ownership state of a resource in the abstract domain.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum OwnershipState {
    ///
    /// path拥有资源
    Owned,
    /// path指向的变量被move掉了
    Moved,
    /// The resource has been dropped (destructor called).
    Dropped,
    /// The resource has been explicitly forgotten and is no longer tracked.
    Forgotten,
    /// The resource is wrapped in `ManuallyDrop` and requires manual destruction.
    ManuallyManaged,
    /// Top: unknown state (used in joins and merging)
    Top,
    /// uinit, can't be access.
    Uinit,
}
