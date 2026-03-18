use crate::analysis::memory::path::Path;
use crate::analysis::numerical::lattice::LatticeTrait;
use crate::analysis::ownership::ownership_state::OwnershipState;
use crate::analysis::ownership::path_uf::PathUnionFind;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct OwnershipCheckError {
    pub message: String,
    pub paths: Vec<Rc<Path>>,
}

impl OwnershipCheckError {
    pub fn new(message: String, paths: Vec<Rc<Path>>) -> Self {
        Self { message, paths }
    }
}

/// An abstract domain that maps memory paths to their `OwnershipState`.
#[derive(Debug, Clone, PartialEq)]
pub struct OwnershipDomain {
    is_top: bool,
    is_bottom: bool,
    pub state_map: HashMap<Rc<Path>, HashSet<OwnershipState>>,
    pub shared_resources: PathUnionFind,
    pub dropped_set: HashSet<Rc<Path>>,
    pub dropped_originals: HashSet<Rc<Path>>,
    pub heap_owner_set: HashSet<Rc<Path>>,
}

impl OwnershipDomain {
    /// Creates a new, empty (bottom) domain.
    pub fn new() -> Self {
        Self::bottom()
    }

    pub fn can_drop(&self, path: &Rc<Path>) -> bool {
        let states = self.get_states(path);

        // 如果包含这些状态，不能 drop
        !states.contains(&OwnershipState::Dropped)
            && !states.contains(&OwnershipState::Moved)
            && !states.contains(&OwnershipState::Forgotten)
            && !states.contains(&OwnershipState::ManuallyManaged)
    }

    pub fn can_forget(&self, path: &Rc<Path>) -> bool {
        let states = self.get_states(path);

        !states.contains(&OwnershipState::Moved)
            && !states.contains(&OwnershipState::Dropped)
            && !states.contains(&OwnershipState::Forgotten)
    }

    pub fn can_use(&self, path: &Rc<Path>) -> bool {
        let states = self.get_states(path);

        // 如果包含这些状态，不能使用
        !states.contains(&OwnershipState::Moved)
            && !states.contains(&OwnershipState::Dropped)
            && !states.contains(&OwnershipState::Uinit)
            && !states.contains(&OwnershipState::Forgotten)
    }

    pub fn is_forgotten_or_root_forgotten(&self, path: &Rc<Path>) -> bool {

        if self.has_state(path, &OwnershipState::Forgotten) {
            return true;
        }

        let root_path = Path::root(path);
        if root_path != *path {
            if self.has_state(&root_path, &OwnershipState::Forgotten) {
                return true;
            }
        }

        false
    }

    /// Gets the ownership states for a given path.
    /// Returns a set containing only `Owned` if the path is not explicitly tracked.
    pub fn get_states(&self, path: &Rc<Path>) -> HashSet<OwnershipState> {
        self.state_map.get(path).cloned().unwrap_or_else(|| {
            let mut set = HashSet::new();
            set.insert(OwnershipState::Owned);
            set
        })
    }

    /// Checks if a path has a specific state.
    pub fn has_state(&self, path: &Rc<Path>, state: &OwnershipState) -> bool {
        self.state_map
            .get(path)
            .map(|states| states.contains(state))
            .unwrap_or(matches!(state, OwnershipState::Owned))
    }

    /// Adds a state to a path's state set.
    pub fn add_state(&mut self, path: Rc<Path>, state: OwnershipState) {
        self.state_map
            .entry(path)
            .or_insert_with(HashSet::new)
            .insert(state);
        self.is_top = false;
        self.is_bottom = false;
    }

    /// Removes a state from a path's state set.
    pub fn remove_state(&mut self, path: &Rc<Path>, state: &OwnershipState) {
        if let Some(states) = self.state_map.get_mut(path) {
            states.remove(state);
            if states.is_empty() {
                self.state_map.remove(path);
            }
        }
    }

    /// Sets the ownership states for a given path (replaces all existing states).
    pub fn set_states(&mut self, path: Rc<Path>, states: HashSet<OwnershipState>) {
        if states.is_empty() {
            self.state_map.remove(&path);
        } else {
            self.state_map.insert(path, states);
        }
        self.is_top = false;
        self.is_bottom = false;
    }

    /// Adds multiple states to a path's state set.
    pub fn add_states(&mut self, path: Rc<Path>, states: HashSet<OwnershipState>) {
        if states.is_empty() {
            return;
        }

        self.state_map
            .entry(path)
            .or_insert_with(HashSet::new)
            .extend(states);
        self.is_top = false;
        self.is_bottom = false;
    }

    /// Removes multiple states from a path's state set.
    pub fn remove_states(&mut self, path: &Rc<Path>, states: &[OwnershipState]) {
        if let Some(current_states) = self.state_map.get_mut(path) {
            for state in states {
                current_states.remove(state);
            }
            if current_states.is_empty() {
                self.state_map.remove(path);
            }
        }
    }

    /// Sets a single state for a path (replaces all existing states).
    pub fn set_state(&mut self, path: Rc<Path>, state: OwnershipState) {
        let mut states = HashSet::new();
        states.insert(state);
        self.set_states(path, states);
    }

    /// Moves the state from an old path to a new path.
    pub fn rename(&mut self, old_path: &Rc<Path>, new_path: &Rc<Path>) {
        if let Some(states) = self.state_map.remove(old_path) {
            self.state_map.insert(new_path.clone(), states);
        }

        if self.dropped_set.remove(old_path) {
            self.dropped_set.insert(new_path.clone());
        }

        if self.dropped_originals.remove(old_path) {
            self.dropped_originals.insert(new_path.clone());
        }

        self.shared_resources.rename(old_path, new_path);
    }

    /// Copies the state from an existing path to a new path.
    pub fn duplicate(&mut self, old_path: &Rc<Path>, new_path: &Rc<Path>) {
        if let Some(states) = self.state_map.get(old_path) {
            self.state_map.insert(new_path.clone(), states.clone());
        }

        if self.dropped_set.contains(old_path) {
            self.dropped_set.insert(new_path.clone());
        }

        if self.shared_resources.contains(old_path) {
            self.shared_resources.union(old_path, new_path);
        }
    }

    /// Removes a path from tracking.
    pub fn forget(&mut self, path: &Rc<Path>) {
        self.state_map.remove(path);
        self.dropped_set.remove(path);
        self.dropped_originals.remove(path);

        self.shared_resources.remove(path);
    }

    pub fn mark_dropped(&mut self, path: Rc<Path>) {
        self.dropped_set.insert(path);
    }

    pub fn is_dropped(&self, path: &Rc<Path>) -> bool {
        self.dropped_set.contains(path)
    }

    pub fn check_double_free(&mut self) -> Vec<OwnershipCheckError> {
        debug!("=== Starting double-free and memory leak check ===");

        let mut errors = Vec::new();

        let all_groups = self.shared_resources.get_all_groups();
        debug!("Found {} resource sharing groups", all_groups.len());

        for group in all_groups {
            if group.len() <= 1 {
                if group.len() == 1 {
                    let path = &group[0];
                    let states = self.get_states(path);

                    if states.contains(&OwnershipState::Forgotten)
                        || states.contains(&OwnershipState::ManuallyManaged)
                    {
                        warn!("Memory leak detected for single path: {:?}", path);
                        errors.push(OwnershipCheckError::new(
                            format!(
                                "[Checker] Possible memory leak: resource at {:?} is forgotten or manually managed",
                                path
                            ),
                            group.clone(),
                        ));
                    } else {
                        debug!("Single path {:?} with states {:?} is OK", path, states);
                    }
                }
                continue;
            }

            debug!(
                "Checking resource group with {} paths: {:?}",
                group.len(),
                group
            );

            let mut owned_or_moved_paths = Vec::new();
            let mut forgotten_or_managed_paths = Vec::new();

            for path in &group {
                let states = self.get_states(path);

                let is_active = states.contains(&OwnershipState::Owned)
                    || states.contains(&OwnershipState::Moved)
                    || states.contains(&OwnershipState::Dropped)
                    || states.contains(&OwnershipState::Top);

                let is_passive = states.contains(&OwnershipState::Forgotten)
                    || states.contains(&OwnershipState::ManuallyManaged);

                if is_active {
                    owned_or_moved_paths.push((path.clone(), states.clone()));
                    debug!("  Path {:?} is active with states {:?}", path, states);
                }
                if is_passive {
                    forgotten_or_managed_paths.push((path.clone(), states.clone()));
                    debug!("  Path {:?} is passive with states {:?}", path, states);
                }
            }

            let total_paths = group.len();
            let active_count = owned_or_moved_paths.len();
            let passive_count = forgotten_or_managed_paths.len();

            debug!(
                "Group summary: {} active paths, {} passive paths",
                active_count, passive_count
            );

            if active_count == 0 && passive_count > 0 {
                warn!(
                    "Memory leak: All {} paths in group are forgotten or manually managed",
                    total_paths
                );
                errors.push(OwnershipCheckError::new(
                    format!(
                        "[Checker] Possible memory leak: all {} paths sharing a resource are forgotten or manually managed",
                        total_paths
                    ),
                    group.clone(),
                ));
                continue;
            }

            if active_count > 1 {

                let mut is_memory_leak = false;

                let has_heap_resource = group.iter().any(|path| self.heap_owner_set.contains(path));

                let has_forgotten = group.iter().any(|path| {
                    let states = self.get_states(path);
                    states.contains(&OwnershipState::Forgotten)
                });

                if has_heap_resource && has_forgotten {
                    is_memory_leak = true;
                    warn!(
                        "Memory leak detected: heap resource aliased with forgotten stack resource in group"
                    );
                }

                if is_memory_leak {
                    warn!(
                        "Memory leak detected: {} paths in group, {} forgotten/passive",
                        active_count, passive_count
                    );

                    let path_list: Vec<String> = group
                        .iter()
                        .map(|p| {
                            let states = self.get_states(p);
                            let is_heap = if self.heap_owner_set.contains(p) {
                                " [HEAP]"
                            } else {
                                ""
                            };
                            format!("{:?} ({:?}){}", p, states, is_heap)
                        })
                        .collect();

                    errors.push(OwnershipCheckError::new(
                        format!(
                            "[Checker] Possible memory leak: heap resource aliased with forgotten stack resource: [{}]",
                            path_list.join(", ")
                        ),
                        group.clone(),
                    ));
                } else {
                    error!(
                        "Double-free detected: {} paths in group have active states (expected ≤1)",
                        active_count
                    );

                    let path_list: Vec<String> = owned_or_moved_paths
                        .iter()
                        .map(|(p, s)| format!("{:?} ({:?})", p, s))
                        .collect();

                    errors.push(OwnershipCheckError::new(
                        format!(
                            "[Checker] Possible double-free: {} paths own the same resource: [{}]",
                            active_count,
                            path_list.join(", ")
                        ),
                        group.clone(),
                    ));
                }
            }
        }

        debug!(
            "=== Finished double-free check, found {} errors ===",
            errors.len()
        );
        errors
    }
}

impl Default for OwnershipDomain {
    fn default() -> Self {
        Self::bottom()
    }
}

impl LatticeTrait for OwnershipDomain {
    fn top() -> Self {
        Self {
            is_top: true,
            is_bottom: false,
            state_map: HashMap::new(),
            shared_resources: PathUnionFind::new(),
            dropped_set: HashSet::new(),
            dropped_originals: HashSet::new(),
            heap_owner_set: HashSet::new(),
        }
    }

    fn is_top(&self) -> bool {
        self.is_top
    }

    fn set_to_top(&mut self) {
        self.state_map.clear();
        self.dropped_set.clear();
        self.dropped_originals.clear();
        self.shared_resources = PathUnionFind::new();
        self.is_top = true;
        self.is_bottom = false;
    }

    fn bottom() -> Self {
        Self {
            is_top: false,
            is_bottom: true,
            state_map: HashMap::new(),
            dropped_set: HashSet::new(),
            shared_resources: PathUnionFind::new(),
            dropped_originals: HashSet::new(),
            heap_owner_set: HashSet::new(),
        }
    }

    fn is_bottom(&self) -> bool {
        self.is_bottom
    }

    fn set_to_bottom(&mut self) {
        self.state_map.clear();
        self.dropped_set.clear();
        self.dropped_originals.clear();
        self.shared_resources = PathUnionFind::new();
        self.is_bottom = true;
        self.is_top = false;
    }

    fn lub(&self, other: &Self) -> Self {
        if self.is_top() || other.is_bottom() {
            return self.clone();
        }
        if other.is_top() || self.is_bottom() {
            return other.clone();
        }

        let mut result = OwnershipDomain::bottom();

        let all_paths: HashSet<_> = self
            .state_map
            .keys()
            .chain(other.state_map.keys())
            .cloned()
            .collect();

        for path in all_paths {
            let states1 = self.get_states(&path);
            let states2 = other.get_states(&path);

            let merged_states: HashSet<OwnershipState> = states1.union(&states2).cloned().collect();

            if !merged_states.is_empty() {
                result.state_map.insert(path, merged_states);
            }
        }

        result.dropped_set = &self.dropped_set | &other.dropped_set;
        result.dropped_originals = &self.dropped_originals | &other.dropped_originals;

        result.shared_resources = self.shared_resources.merge(&other.shared_resources);

        result.is_bottom = false;
        result
    }

    fn widening_with(&self, other: &Self) -> Self {
        self.lub(other)
    }
}
