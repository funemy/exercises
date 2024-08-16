// A simple example showing a weird reborrow case
// The explanation for this code is based on NLL borrow checker.
// I'm not sure if this is also the same for polonius
//
// For a detailed reference, see here: https://rust-lang.github.io/rfcs/2094-nll.html#reborrow-constraints
enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

// The question we ask here is -- why doesn't this code type check?
// We answer this question by first annotating all the lifetime constraints.
// For a constraint 'x : 'y, it means 'x lives **longer** (i.e., outlives) 'y.
fn insert<'a,'b>(mut l : &'a mut List<&'b mut i32>, mut n : &'b mut i32) {
  // el : &'x mut &'b mut i32
  // 'a : 'x
  while let List::Cons(el, tl) = l {
    // tmp = &mut **el : &'z mut i32
    // 'x : 'z
    // 'b : 'z
    let tmp = &mut **el;
    // 'b : 'b
    *el = n;
    // 'z : 'b
    n = tmp;
    l = &mut* tl
  }
}
// we mark the relevant lifetimes and their constraints in the code above.
// 'x is the lifetime of the head of the list (i.e., `el`)
// 'z is the lifetime of our temporary variable `tmp.
// Whenever we assign a reference to another, the rhs must outlives the lhs,
// otherwise, the rhs might be dropped while lhs still alive, which cause a
// memory safety issue.
//
// Most constraints are generated based on the assignment rule.
// The tricky part of our example is line 21, where a reborrow happens.
// A reborrow is when we deref an reference then immediate take a reference
// (or mutable reference) out of it.
// The motivation for doing this is that mutable references cannot be copied,
// but we might want to temporarily hand over a mutable reference to another
// variable then return the control over this mutable reference later.
//
// Whenever such reborrow happens, Rust compiler first compute what's called
// "supporting prefix", which are enumerated by striping away fields and derefs
// until we can no longer do so or reaching a deref of shared reference.
// (Intuitively, this is because shared references can be copied).
// In line 21, we are taking a mutable reference (i.e., reborrowing) `**el`.
// The supporting prefixes are:
// **el
// *el
// el
// Among the three prefixes, el is not a deref lvalue, whereas **el and *el are.
// **el as a deref lvalue, its reference *el has the lifetime 'b
// *el as a deref lvalue, its reference el has the lifetime 'x
// For each of those lifetime, we generate an outlive constraint, they are
// 'b : 'z and 'x : 'z, correspondingly.
//
// Now we see how all the lifetime constraints are generated, we can compute a
// transitive closure out of them.
// Since we have 'a : 'x, 'x : 'z, and 'z : 'b, by transitivity, we have 'a : 'b,
// meaning 'a should outlives 'b.
// However, this constraint cannot be proven based on the provided type.
// (From the function type signature, all we know from the type of `l` is that 'b
// must outlive 'a, but not the other way)
//
// As a result, this code doesn't compile, and the compiler suggests that we
// need to add the required lifetime constraint in the function type.
//
//
// Now by adding the lifetime constraint, this code surely compiles.
// But let's think about a more interesting question:
// For the current code (which doesn't compile), does the compiler
// reject us because there's some fundamental safety issue, or because
// the type system is overly constrained?
//
// This is a much harder to answer question.
//
// First, this function is definitely not doing an insertion one would
// expect.
// The function insert `n` to the head, then push all existing element
// backwards, and finally storing the last element of the list in `n`
// when the function returns.
//
// But what could go wrong if such code gets accepted?
// Well, the root cause of the compiler error originates from `tmp`
// reborrowing `el`.
// Intuitively, since `tmp` is storing the element of the list in
// the current iteration, it's lifetime should be no longer than list
// elements' lifetime, i.e., 'b. (In fact they should just be 'b)
// But why should it also be shorter than 'x (hence transitively shorter
// than 'a)?
//
// I don't have a good intuition here.
// But let's see what will happen if we remove the constraint 'x : 'z
// on line 19.
//
// Well, that means 'z can potentially be longer than 'x or 'a.
// Since lifetime captures "how long" a reference can be used,
// if 'a got expired, that unblocks the usage of the list, meaning
// we can access the element of the lists, which are mutable references
// to some integers of lifetime 'b.
// But we also have `tmp` as mutable references to those integers.
// So potentially we can leak tmp out of `insert0`, then some integers
// might have more than one mutable reference, which is exactly what Rust
// wants to avoid!

fn main() {
    let mut y = 42;
    let my = &mut y;

    let mut x = 0;
    let mx = &mut x;
    let mut l = List::Cons(&mut *mx, Box::new(List::Nil));

    insert0(&mut l, &mut *my);

    drop(l);
    println!("{:?}", mx);
    println!("{:?}", my);
}
