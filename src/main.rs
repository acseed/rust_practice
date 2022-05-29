mod ds;

use ds::rbtree::RBTree;

fn main() {
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
    let v = tree.get(&"E".to_string());
    println!("value is {:?}", v);
}

