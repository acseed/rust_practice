use std::cell::{Ref, RefCell};
use std::{fmt, ptr};
use std::fmt::{Display, Formatter};
use std::rc::{Rc, Weak};

type Link<K, V> = Rc<RefCell<Node<K, V>>>;
type Tree<K, V> = Option<Link<K, V>>;

type WeakLink<K, V> = Weak<RefCell<Node<K, V>>>;
type WeakTree<K, V> = Option<WeakLink<K, V>>;

type RBEntry<K, V> = Rc<Entry<K, V>>;

#[derive(Clone, Debug, PartialEq)]
enum Color {
    Red, Black
}

#[derive(PartialEq)]
enum RBOperation {
    Left,
    Right,
}

#[derive(Debug, Clone)]
struct Entry<K, V> {
    key: K,
    value: RefCell<Option<V>>,
}

impl <K, V> Entry<K, V> {
    fn new(key: K, value: V) -> Rc<Entry<K, V>> {
        Rc::new(Entry {
            key,
            value: RefCell::new(Some(value)),
        })
    }

    fn borrow_value(&self) -> Ref<V> {
        Ref::map(self.value.borrow(), |it| it.as_ref().unwrap())
    }
}

impl<K: ToString + Display, V: ToString + Display> ToString for Entry<K, V> {
    fn to_string(&self) -> String {
        let mut v = Vec::<String>::new();
        v.push("[(".to_string());
        v.push(self.key.to_string());
        v.push(")->(".to_string());
        let val = self.value.borrow();
        if val.is_none() {
            v.push("None".to_string());
        } else {
            v.push(val.as_ref().unwrap().to_string());
        }
        v.push(")]".to_string());
        return v.join("");
    }
}

#[derive(Clone, Debug)]
struct Node<K, V> {
    pub color: Color,
    pub entry: RBEntry<K, V>,
    pub parent: Tree<K, V>,
    left: Tree<K, V>,
    right: Tree<K, V>,
}

impl<K, V> Node<K, V> where K: Ord + Clone + Display,
                            V: Clone + Display {
    pub fn new(key: K, value: V) -> Node<K, V> {
        Node {
            color: Color::Red,
            entry: Entry::new(key, value),
            parent: None,
            left: None,
            right: None,
        }
    }

    fn new_tree(self) -> Tree<K, V> {
        Some(Rc::new(RefCell::new(self)))
    }
}

#[derive(Debug, Clone)]
pub struct RBError {
    pub message: String
}

impl Display for RBError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for RBError {
    fn description(&self) -> &str {
        &self.message
    }
}

type RBResult<T> = Result<T, RBError>;

/// from introduction to algorithms:
/// 1. Every node is either red or black.
/// 2. The root is black.
/// 3. Every leaf(NIL) is black.
/// 4. If a node is red,then both its children are black.
/// 5. For each node, all simple paths from the node to descendant
///    leaves contain the same number of black nodes.
pub struct RBTree<K, V> {
    root: Tree<K, V>,
    length: usize,
}

impl<K, V> RBTree<K, V> where K: Ord + Clone + Display + ToString, V: Clone + Display + ToString {
    pub fn new() -> RBTree<K, V> {
        RBTree {
            root: None,
            length: 0
        }
    }

    // insert (key, value) pair into the tree
    // if there the key exist, then update the value inplace accordingly
    pub fn insert(&mut self, key: K, value: V) {
        let node = Node::new(key, value).new_tree();
        let result = self.insert_node(node);
        if let Ok(_) = result {
            self.length += 1;
        }
    }

    /// as retrieve value from local variable 'entry' violate the lifetime rule,
    /// so use unsafe
    pub fn get(&self, key: &K) -> Option<&V> {
        let result = self.inner_get(&self.root, key);
        match result {
            Some(entry) => {
                unsafe {
                    Some((*entry.value.as_ptr()).as_ref().unwrap() )
                }
            },
            _ => None
        }
    }

    fn inner_get(&self, root: &Tree<K, V>, key: &K) -> Option<RBEntry<K, V>> {
        let mut x = root.clone() as Tree<K, V>;
        while x.is_some() {
            let entry = self.entry(&x);
            if &entry.key == key {

                return Some(entry.clone());
            } else {
                let dir = self.which_operation_key(&entry.key, &key);
                match dir {
                    RBOperation::Left => x = self.left_child(&x),
                    RBOperation::Right => x = self.right_child(&x),
                }
            }
        }
        None
    }

    // insert z to the tree
    fn insert_node(&mut self, node: Tree<K, V>) -> RBResult<Tree<K, V>> {
        let mut x = self.root.clone() as Tree<K, V>;
        let mut y= None as Tree<K, V>;
        let z = node;

        // find the appropriate position for z
        // y is the parent
        while x.is_some() {
            y = x.clone();
            let x_entry = self.entry(&x);
            let z_entry = self.entry(&z);
            if x_entry.key == z_entry.key {
                let value = z_entry.value.replace(None);
                self.set_entry_value(&x, value);
                return Err(RBError {
                    message: "key already exist, updated in place".to_string()
                })
            }
            match self.which_operation(&x_entry, &z_entry) {
                RBOperation::Left => {
                    x = self.left_child(&x);
                },
                RBOperation::Right => {
                    x = self.right_child(&x)
                },
            }
        }
        self.set_parent(&z, y.clone());

        // if y is none, thereby z is the first node, thus the root is z
        if y.is_none() {
            self.root = z.clone();
        } else {
            self.set_child(&y, z.clone(), self.which_operation(&self.entry(&y), &self.entry(&z)));
        }
        self.insert_fixup(z.clone());
        Ok(z.clone())
    }

    fn insert_fixup(&mut self, z: Tree<K, V>) {
        let mut z = z;
        let mut p = self.parent(&z);
        while p.is_some() && self.color(&p) == Color::Red {
            // grandparent is always exist
            let pp = self.parent(&p);
            match self.which_child(&pp, &p) {
                RBOperation::Left => {
                    let uncle = self.right_child(&pp);
                    if uncle.is_some() && self.color(&uncle) == Color::Red {
                        self.set_color(&p, Color::Black);
                        self.set_color(&uncle, Color::Black);
                        self.set_color(&pp, Color::Red);
                        continue;
                    } else {
                        let which_child = self.which_child(&p, &z);
                        if which_child == RBOperation::Right {
                            self.left_rotate(&p);
                            z = p.clone();
                            p = self.parent(&z);
                        }
                        self.set_color(&pp, Color::Red);
                        self.set_color(&p, Color::Black);
                        self.right_rotate(&pp);
                    }
                },
                RBOperation::Right => {
                    let uncle = self.left_child(&pp);
                    if uncle.is_some() && self.color(&uncle) == Color::Red {
                        self.set_color(&p, Color::Black);
                        self.set_color(&uncle, Color::Black);
                        self.set_color(&pp, Color::Red);
                        continue;
                    } else {
                        let which_child = self.which_child(&p, &z);
                        if which_child == RBOperation::Left {
                            self.right_rotate(&p);
                            z = p.clone();
                            p = self.parent(&z);
                        }
                        self.set_color(&pp, Color::Red);
                        self.set_color(&p, Color::Black);
                        self.left_rotate(&pp);
                    }
                }
            }
        }
        self.set_color(&self.root, Color::Black);
    }

    fn left_rotate(&mut self, x: &Tree<K, V>) {
        let x = x.clone();
        let y = self.right_child(&x);
        let parent = self.parent(&x);

        // node x's right child is node y's left child
        let xr = match y {
            Some(ref y) => self.left_child(&Some(y.clone())),
            _ => None
        };
        self.set_child(&x, xr, RBOperation::Right);

        //node y's left child's parent is x
        let yl = self.left_child(&y);
        if yl.is_some() {
            self.set_parent(&yl, x.clone());
        }

        if parent.is_none() {
            self.root = y.clone();
        }

        // node y's parent is node x's parent
        self.set_parent(&y, parent.clone());

        // parent's left or right child is y
        self.set_parent_dir(&parent, &x, &y);

        //node y's left child is x
        self.set_child(&y, x.clone(), RBOperation::Left);

        //node x's parent is y
        self.set_parent(&x, y.clone());
    }

    fn right_rotate(&mut self, x: &Tree<K, V>) {
        let x = x.clone();
        let y = self.left_child(&x);
        let parent = self.parent(&x);

        // node x's left is node y's right child
        let xl = match y {
            Some(ref y)  => self.right_child(&Some(y.clone())),
            _ => None
        };
        self.set_child(&x, xl, RBOperation::Left);

        // node y's right child's parent is x
        let yr = self.right_child(&y);
        if yr.is_some() {
            self.set_parent(&yr, x.clone());
        }

        if parent.is_none() {
            self.root = y.clone();
        }

        // node y's parent is x's parent
        self.set_parent(&y, parent.clone());

        // parent's left or right child is y
        self.set_parent_dir(&parent, &x, &y);

        // x is y's right child
        self.set_child(&y, x.clone(), RBOperation::Right);

        // x's parent is y
        self.set_parent(&x, y.clone());
    }

    fn set_parent_dir(&self, parent: &Tree<K, V>, x: &Tree<K, V>, y: &Tree<K, V>) {
        if let Some(parent) = parent {
            let direction = self.which_operation(
                &self.entry(&Some(parent.clone())), &self.entry(&x));
            match direction {
                RBOperation::Left => parent.borrow_mut().left = y.clone(),
                RBOperation::Right => parent.borrow_mut().right = y.clone(),
            }
        } else {
            self.set_parent(&y, None);
        }
    }

    fn left_child(&self, x: &Tree<K, V>) -> Tree<K, V> {
        x.as_ref().unwrap().borrow().left.clone()
    }

    fn right_child(&self, x: &Tree<K, V>) -> Tree<K, V> {
        x.as_ref().unwrap().borrow().right.clone()
    }

    fn parent(&self, x: &Tree<K, V>) -> Tree<K, V> {
        x.as_ref().unwrap().borrow().parent.clone()
    }

    fn entry(&self, x: &Tree<K, V>) -> RBEntry<K, V> {
        x.as_ref().unwrap().borrow().entry.clone()
    }

    fn set_entry_value(&self, x: &Tree<K, V>, value: Option<V>) {
        let _ = x.as_ref().unwrap().borrow().entry.value.replace(value);
    }

    fn set_color(&self, x: &Tree<K, V>, color: Color) {
        x.as_ref().unwrap().borrow_mut().color = color;
    }

    fn set_parent(&self, x: &Tree<K, V>, parent: Tree<K, V>) {
        x.as_ref().unwrap().borrow_mut().parent = parent;
    }

    fn color(&self, x: &Tree<K, V>) -> Color {
        x.as_ref().unwrap().borrow().color.clone()
    }

    fn set_child(&self, x: &Tree<K, V>, child: Tree<K, V>, dir: RBOperation) {
        match dir {
            RBOperation::Left => x.as_ref().unwrap().borrow_mut().left = child,
            RBOperation::Right => x.as_ref().unwrap().borrow_mut().right = child
        }
    }

    fn which_child(&self, p: &Tree<K, V>, c: &Tree<K, V>) -> RBOperation {
        let left = self.left_child(p);
        if left.is_none() {
            return RBOperation::Right;
        }
        let left = left.as_ref().unwrap();
        let child = c.as_ref().unwrap();
        if ptr::eq(left.as_ptr(), child.as_ptr()) {
            RBOperation::Left
        } else {
            RBOperation::Right
        }
    }

    fn which_operation(&self, p: &RBEntry<K, V>, x: &RBEntry<K, V>) -> RBOperation {
        self.which_operation_key(&p.key, &x.key)
    }

    fn which_operation_key(&self, pkey: &K, xkey: &K) -> RBOperation {
        if xkey <= pkey {
            RBOperation::Left
        } else {
            RBOperation::Right
        }
    }

    pub fn print_tree(&self) {
        println!("start-----------------------------------");
        self.do_print_tree(self.root.clone(), 0, "Root".to_string());
        println!("end-------------------------------------");
        println!();
    }

    fn do_print_tree(&self, x: Tree<K, V>, height: i32, prefix: String) {
        match x {
            Some(ref xx) => {
                let spaces = height * 4;
                let mut sv = Vec::<String>::new();
                for _ in 0..spaces {
                    sv.push(" ".to_string());
                }
                sv.push(prefix);
                let entry = self.entry(&x);
                let s = entry.to_string();
                sv.push(s);
                match xx.borrow().color {
                    Color::Red => sv.push(" [RED]".to_string()),
                    Color::Black => sv.push(" [BLACK]".to_string()),
                }
                println!("{}", sv.join(""));
                let left = self.left_child(&x);
                let right = self.right_child(&x);
                self.do_print_tree(left, height + 1, "L".to_string());
                self.do_print_tree(right, height + 1, "R".to_string());
            },
            _ => (),
        }
    }
}

#[test]
fn test() {
    let mut tree = RBTree::<String, i32>::new();
    tree.insert("A".to_string(), 1);
    tree.print_tree();
    tree.insert("B".to_string(), 2);
    tree.print_tree();
    tree.insert("C".to_string(), 3);
    tree.print_tree();
    tree.insert("D".to_string(), 4);
    tree.print_tree();
    tree.insert("A".to_string(), 4);
    tree.print_tree();
    tree.insert("A".to_string(), 4);
    tree.print_tree();
}



