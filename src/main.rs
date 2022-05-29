mod ds;

use ds::rbtree::RBTree;

fn main() {
    let mut tree = RBTree::<String, i32>::new();
    tree.insert("A".to_string(), 1);
    tree.insert("B".to_string(), 2);
    tree.insert("C".to_string(), 3);
    tree.insert("D".to_string(), -1);
    tree.insert("A".to_string(), -123);
    tree.insert("E".to_string(), 5);
    tree.print_tree();
    let x = tree.successor(&"D".to_string());
    println!("{:?}", x);
}

