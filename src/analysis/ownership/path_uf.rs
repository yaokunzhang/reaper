use crate::analysis::memory::path::Path;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub struct PathUnionFind {
    parent: HashMap<Rc<Path>, Rc<Path>>,
    rank: HashMap<Rc<Path>, usize>,
}

impl PathUnionFind {
    pub fn new() -> Self {
        Self {
            parent: HashMap::new(),
            rank: HashMap::new(),
        }
    }

    pub fn find_group(&self, path: &Rc<Path>) -> Vec<Rc<Path>> {
        let root = self.find(path);

        self.parent
            .keys()
            .filter(|p| self.find(p) == root)
            .cloned()
            .collect()
    }

    pub fn find(&self, path: &Rc<Path>) -> Rc<Path> {
        if !self.parent.contains_key(path) {
            return path.clone();
        }

        let mut current = path.clone();
        while let Some(parent) = self.parent.get(&current) {
            if parent == &current {
                break;
            }
            current = parent.clone();
        }
        current
    }

    pub fn find_mut(&mut self, path: &Rc<Path>) -> Rc<Path> {
        if !self.parent.contains_key(path) {
            self.parent.insert(path.clone(), path.clone());
            self.rank.insert(path.clone(), 0);
            return path.clone();
        }
        let parent = self.parent.get(path).unwrap().clone();
        if parent != *path {
            let root = self.find_mut(&parent);
            self.parent.insert(path.clone(), root.clone());
            return root;
        }

        path.clone()
    }

    pub fn union(&mut self, path1: &Rc<Path>, path2: &Rc<Path>) {
        let root1 = self.find_mut(path1);
        let root2 = self.find_mut(path2);

        if root1 == root2 {
            return; 
        }

        let rank1 = *self.rank.get(&root1).unwrap_or(&0);
        let rank2 = *self.rank.get(&root2).unwrap_or(&0);

        match rank1.cmp(&rank2) {
            std::cmp::Ordering::Less => {
                self.parent.insert(root1, root2);
            }
            std::cmp::Ordering::Greater => {
                self.parent.insert(root2, root1);
            }
            std::cmp::Ordering::Equal => {
                self.parent.insert(root2, root1.clone());
                self.rank.insert(root1, rank1 + 1);
            }
        }
    }

    pub fn is_connected(&self, path1: &Rc<Path>, path2: &Rc<Path>) -> bool {
        self.find(path1) == self.find(path2)
    }

    pub fn connected(&mut self, path1: &Rc<Path>, path2: &Rc<Path>) -> bool {
        self.find_mut(path1) == self.find_mut(path2)
    }

    pub fn get_group(&self, path: &Rc<Path>) -> Vec<Rc<Path>> {
        self.find_group(path)
    }

    pub fn rename(&mut self, old_path: &Rc<Path>, new_path: &Rc<Path>) {
        if let Some(old_root) = self.parent.get(old_path).cloned() {
            if &old_root == old_path {
                let children: Vec<_> = self
                    .parent
                    .iter()
                    .filter(|(_, parent)| *parent == old_path && *old_path != **parent)
                    .map(|(child, _)| child.clone())
                    .collect();

                for child in children {
                    self.parent.insert(child, new_path.clone());
                }

                if let Some(rank) = self.rank.remove(old_path) {
                    self.rank.insert(new_path.clone(), rank);
                }
            } else {
                self.parent.insert(new_path.clone(), old_root);
            }

            self.parent.remove(old_path);
            self.rank.remove(old_path);
        }
    }

    pub fn contains(&self, path: &Rc<Path>) -> bool {
        self.parent.contains_key(path)
    }

    pub fn remove(&mut self, path: &Rc<Path>) {
        self.parent.remove(path);
        self.rank.remove(path);
    }

    pub fn merge(&self, other: &PathUnionFind) -> PathUnionFind {
        let mut result = PathUnionFind::new();

        for (path, parent) in &self.parent {
            result.parent.insert(path.clone(), parent.clone());
        }
        for (path, rank) in &self.rank {
            result.rank.insert(path.clone(), *rank);
        }

        for group in other.get_all_groups() {
            if group.len() > 1 {
                let first = &group[0];
                for path in &group[1..] {
                    result.union(first, path);
                }
            }
        }

        result
    }

    pub fn clear(&mut self) {
        self.parent.clear();
        self.rank.clear();
    }

    pub fn is_empty(&self) -> bool {
        self.parent.is_empty()
    }

    pub fn all_paths(&self) -> Vec<Rc<Path>> {
        self.parent.keys().cloned().collect()
    }

    pub fn get_all_groups(&self) -> Vec<Vec<Rc<Path>>> {
        let mut groups: HashMap<Rc<Path>, Vec<Rc<Path>>> = HashMap::new();

        for path in self.parent.keys() {
            let root = self.find(path);
            groups.entry(root).or_insert_with(Vec::new).push(path.clone());
        }

        groups.into_values().collect()
    }
}

impl Default for PathUnionFind {
    fn default() -> Self {
        Self::new()
    }
}