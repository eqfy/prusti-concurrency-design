# Supporting Concurrency Via Threads in Prusti

## Introduction
As a programming language focusing on safety and efficiency, safe concurrency is a distinguishing difference between Rust and older languages like C. Safe concurrency is also heavily used in many applications to boost efficiency. 

Despite Rust's advanced features for safe concurrency, Rust is unable to prove program correctness. As an automatic program verifier based on the Viper infrastructure, Prusti allows Rust programmer to easily specify their programs for automatic formal verification. 

This document discusses the design and implementation of extending Prusti with capabilities to verify concurrent programs using threads. It contains the following 4 sections:

1. [Specification Syntax](##Specification-Syntax)
2. [Viper Encoding](##Viper-Encoding)
3. [Parsing and type checking Implementation](##Parsing-and-type-checking)
5. [MIR to Viper Implementation](##Encoding-MIR-to-Viper-(TODO))

#### Unsupported usages:
+ Instantiating threads with a closure not defined in the spawn
+ Using old expressions in `#[ensures(...)]` when returning JoinHandles of threads

## Specification Syntax

### Thread spawn and join in the same function

In general, the specification of threads is a straightforward specification of the post-condition (i.e. what happens after the thread joins). Normally, a thread is spawned by passing in a zero-argument closure as the argument. In our case, the specifications are appended before this closure. [Fig 1](#####Fig-1) shows a general case of how the specification is used. 

Note that an additional specificaton for specifying the return type might be included in the future (line 18). (see [common issue](####Return-type-issue:))

##### Fig 1
```rust=
#![feature(register_tool)]
#![register_tool(prusti)]
// The following compiler flags are necessary for proc_macros 
// to work at expression positions with custom attributes
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

// The necessary imports
extern crate prusti_contracts;
use prusti_contracts::*;
use std::thread; // can be inlined as well
...
fn test() {
    // Spawning the thread
    // Note we can still provide a postcondition without the let statement
    let t = thread::spawn(
        #[t_ensures(...)]
        // #[t_type(the_return_type)] might be added.
        || {
            // The thread body
            ...
        }
    );
    ...
    // Joining the thread
    t.join().unwrap();
}
...
```

It was decided to not allow the user to specify pre-conditions because threads are spawned (forked) in Rust. Rust threads are created generally with the `thread::spawn(|| {})` syntax, where the closure is in an inline position. This makes specifications for pre-conditions mostly redundant. Alternatively, the user can also pass in a closure, but this is rarely used in practice.

The following ([Fig 2](#####Fig-2)) is a basic example where the `#[t_ensures(...)]` before the closure (line 9) makes sure that the `x` captured will be one more than its original by the time the thread is joined. The `old(x)` used in the specifications refers to the state of x when it is captured by the closure. 

Note that `old()` is not supported in some cases (see [unsupported usages](####Unsupported-usages)).

##### Fig 2
```rust=
...
#[requires(true)]
#[ensures(result == 2)]
fn add1() -> i32 {
    let x: i32 = 1;
    let t: JoinHandle<i32> = thread::spawn(
        // old() refers to the state of x when it's captured by the closure
        #[t_ensures(result == old(x) + 1)]
        move || { 
            x = x + 1
    });
    let res: i32 = t.join().unwrap();
    res
}
...
```

### Thread spawn and join in separate functions
Sometimes, the user may want to have the spawn a thread in a separate function and return the `JoinHandle<T>` to the thread spawned. In these cases, we allow users to include a thread's postcondition into the postcondition of the Rust function with the `on_join()` syntax.

Currently, this only specification only supports one state assertion so `old()` statements cannot be used. The reason behind this is because the Viper backend we use to verify our program does not support passing labels of states yet.

##### Fig 3a
```rust=
...
#[requires(x > 0)]
#[ensures(on_join(result > 0))]
fn spawn_add1(x : i32) -> JoinHandle<i32> {
    // What if there is x is changed here?
    let t: JoinHandle<i32> = thread::spawn(
        #[t_ensures(result > 0)]
        move || {
            x = x + 1
    });
    ...
    t
}
...
```
In the above example (Fig 3a), the value of x might be changed before the spawning of a thread. In simple cases, we can alter our function's post-condition (Fig 3b). Though this example is not technically supported right now because it uses `old` statements.

##### Fig 3b
```rust=
...
#[requires(x > 0)]
#[ensures(on_join(result == old(x + 1) * 2))]
fn spawn_add1times2(x : i32) -> JoinHandle<i32> {
    x = x + 1; // x is changed here
    let t: JoinHandle<i32> = thread::spawn(
        #[t_ensures(result == old(x) * 2)]
        move || {
            x = x + 1
    });
    ...
    t
}
...
```

In the future, Prusti is also likely to support a function returning some collection of `JoinHandles<T>`. The envisioned syntax will look like `on_join[n]` (n is some integer) with the `[ ]` operator referring to the postcondition of the thread in the order that they are added. (Fig 3c)

##### Fig 3c
```rust=
#[requires(x > 0)]
#[ensures(on_join[0](result > 0) && on_join[1](...) && ...)]
fn spawn_add1(x : i32) -> Vec<JoinHandle<i32>> {
    // What if there is x is changed here?
    let t1: JoinHandle<i32> = thread::spawn(
        #[t_ensures(result > 0)]
        move || {
            x = x + 1
    });
    let t1: JoinHandle<i32> = thread::spawn(
        ...
    });
    ...
    vec![t1, t2]
}
...
```

## Viper Encoding
In Prusti, the Viper encoding is generated from MIR code, which is in turn generated by rustc (the Rust compiler) from Rust source code. Hence, the example Viper encodings from this document are not the precise Viper encoding that will be generated. Nonetheless, the core idea for the encoding threads is unchanged.

The following example shows how a [Fig 2](#####Fig-2) is encoded into Viper by hand.

##### Fig 4a

```=
predicate join_handle(self: Ref)

method simple_thread(x: Ref) returns (res: Ref)
    requires i32(x)
    requires unfolding i32(x) in (x.val_int) > 0
    ensures i32(res)
    ensures unfolding i32(res) in (res.val_int) == old(unfolding i32(x) in (x.val_int) + 1)
{
    // Inline thread and verify
    label l0;
    var t0: Ref
    var b : Bool
    b := havoc_bool()
    if (b) {
        exhale forall i:Ref :: perm(i32(i)) > none && i != x  ==> acc(i32(i), perm(i32(i)))
        unfold i32(x)
        x.val_int := x.val_int + 1
        fold i32(x)
        exhale i32(x) && unfolding i32(x) in (x.val_int) == old[l0](unfolding i32(x) in (x.val_int) + 1)
        assume false
    } else {
        exhale i32(x)
        inhale join_handle(t0) --* i32(x) && unfolding i32(x) in (x.val_int) == old[l0](unfolding i32(x) in (x.val_int) + 1)
    }
    // Joining a thread
    inhale join_handle(t0)
    apply join_handle(t0) --* i32(x) && unfolding i32(x) in (x.val_int) == old[l0](unfolding i32(x) in (x.val_int) + 1)
    inhale i32 (res)
    unfold i32(res)
    unfold i32(x)
    res.val_int := x.val_int
    fold i32(x)
    fold i32(res)
}
```

We use an inline approach to encoding threads in Viper. Specifically, the `thread::spawn(|| {...})` is translated into a big if-else statement. The if-else depends on a `havoc_bool()`, which means that Viper will have to go down both branches. 

The true branch (line 14) is designed to simulate the case when a thread is being executed and checks if the postconditions are met. Therefore, it must contain what's inside the closure in the original Rust code. In addition, three extra components have been added. The first component is the `exhale forall` which exhales all permissions except for identifiers captured by the closure. This step is added to make sure that the thread fails to verify if it uses any identifier that lacks permissions. The second component is the exhale statement, which serves to check if the postconditions specified are satisfied. If the postconditions are not met, Viper will raise an error here. Finally, an `assume false` is appended to invalidate any changes made in this branch.

The else branch (line 21) represents the case when we are ambiguous about whether or not the thread has executed. However, in the case that the true branch does not raise any errors, we can safely assume that by the time we join the thread, the postconditions are satisfied. This is represented in the else branch with the `inhale` statement. To elaborate, we inhale a magic wand that states if a thread has joined, we can get back its postcondition.

### An alternative encoding
Rather than trying to inline the code, it might b feasible to simply create a new method for verifying the thread body. In this case, it would look something like the following. The main advantage of this approach is that it resembles the MIR more than the previous approach. Moreover, there is no need to generate manual exhales like [Fig 4a](#####Fig-4a), line 15. Replacing the manual exhales would be finding the precondition of the method used for thread closure verification, which might be easier to do.

##### Fig 4b
```=
...
predicate join_handle(self: Ref)

method simple_thread(x: Ref) returns (res: Ref)
    requires i32(x)
    requires unfolding i32(x) in (x.val_int) > 0
    ensures i32(res)
    ensures unfolding i32(res) in (res.val_int) == old(unfolding i32(x) in (x.val_int) + 1)
{
    // Inline thread and verify
    label l0;
    var t0: Ref
    // Spawning a thread
    t0 := thread_closure_body(x)
    // Joining a thread
    inhale join_handle(t0)
    apply join_handle(t0) --* i32(x) && unfolding i32(x) in (x.val_int) == old[l0](unfolding i32(x) in (x.val_int) + 1)
    inhale i32 (res)
    unfold i32(res)
    unfold i32(x)
    res.val_int := x.val_int
    fold i32(x)
    fold i32(res)
}

method thread_closure_body(x: Ref) returns (t: Ref)
    requires i32(x)
    ensures join_handle(t) --* i32(x) && unfolding i32(x) in (x.val_int) == old(unfolding i32(x) in (x.val_int) + 1)
{
    // The closure body goes here
    unfold i32(x)
    x.val_int := x.val_int + 1
    fold i32(x)
    inhale joinable(t)
    // Checks the thread postcondition with the package statement
    package joinable(t) --* i32(x) && unfolding i32(x) in (x.val_int) == old(unfolding i32(x) in (x.val_int) + 1)
}
```

## Parsing and type checking
This section covers the implementation details for parsing and typchecking the specifications.
This is the necessary step before we can continue to encoding Viper functions for verification. 

### Overview of workflow 
1. The prusti-rustc binary receives a Rust program for verification and does initial environment checking
2. The prusti-driver binary invokes rust compiler on the targeted program for verification
3. During expansion, rustc uses crates `prusti-contracts`, `prusti-contracts`, `prusti-contracts`, and `prusti-specs` for parsing of specifications and rewriting of the program
4. After rustc completes analysis (type checking) of the rewritten program, specifications are collected and attached to their respective items (e.g. function, loop, closure...) ([Relating specs to Rust items](###Relating-specs-to-Rust-items))

### Overview of crates and important files
#### prusti-contracts
This crate exposes user facing procedural macro like `#[requires(...)]`, `#[ensures(...)]`, and `invariant!(...)` and `#[t_ensures(...)]`. These macros generate `#[prusti::*]` attributes for use in prusti-contracts-internal.  

#### prusti-contracts-impl
This is the crate for specially treating macros that needs the proc-macro-hack. However, it may be outdated (see [Choice of macros](###Choice-of-macros)). 

#### prusti-contracts-internal
This crate contains a single procedural macro that consumes `#[prusti::*]` and calls relevant macros in `prusti-specs` to add code for type checking specifications

#### prusti-specs
This crate contains the main implementation logic for parsing and type checking.

+ lib.rs
    + This file contains the main code for generating the dummy functions using procedural macros. It is called by `prusti-contracts-internal`.
+ rewriter.rs
    + This file contains the helper functions (technically procedural macros) for rewriting the specifications
    + `generate_spec_item_fn(...)` and  `generate_loop_invariant_fn(...)` are the entry points behind behind generating dummy functions and each call different things
    + This file uses structs, types and functions from the `specifications/*` folder for parsing and rewriting of independent specificatins
+ specifications/common.rs
    + This file contains definitions of specification data structures. 
    + SpecID and ExprID are also defined and generated here. 
        + SpecID corresponds to an entire specification
        + ExprID corresponds to each individual assertion in a specification 
+ specifications/untyped.rs
    + The purpose is to go over an assertion and encode type checking information appropriately depending on the `AssertionKind` with the `encode_type_check(...)` function
    + Defines `AssertionKind`, and different encoding strategies for each
    + Modification needed to support `on_join(...)`
+ specifications/preparser.rs
    + Main purpose is to split a composite Prusti assertion into atomic assertions, parses the resulting Rust expressions with syn, and finally reassemble composite Prusti assertions.
    + Called only by `untyped.rs` when a new parser is new parser is created with the `from_token_stream(tokens)` function
    + Creates the ParserStream struct which is a helper struct for handling the tokenstream
    + The entry function is  `extract_assertion(...)`
    + Modification needed to support `on_join(...)`
+ specifications/json.rs
    + This generates json from the parsed specifications with `to_structure(&self)`
    + All types defined in `untyped.rs` implements the `ToStructure<T>` trait
    + Used for storing specification information for the later stage of connecting specifications to their respective Rust items after type checking.


### Rewriting strategy for type checking
#### Current approach

The current approach for rewriting inputs for compiler typechecking is very similar to how it is completed for loop invariants. The assertions contained in the specification is placed in an `if false` block so that the rust compiler can perform typechecking for us. An unique `spec_id` is assigned for each `#[t_ensures(...)]` assertion. Each assertion will contain one or many expressions separated by conjunctions (`&&`). Every expression will then get assigned to some `expr_id` and some closure for typechecking.

One shortcoming of the current design is that the user must specify the return type of the closure explicitly. The reason for doing this is becuase there is no way of getting the return type information from the Rust compiler until the compiler finishes source code analysis (which occurs much later). In the future, this restriction will likely be lifted and the typechecking of thread postconditions will be postponed to a later phase when we can query from compiler the necessary information.

Input: 
```rust=
fn test (x : i32) {
    let t = thread::spawn(
        #[t_ensures(result > 0)]
        move || -> i32 {  // return type for closure is manually specified
            x = x + 1;
            x
    });
    t.join().unwrap();
}
```

Rewritten output:
```rust=
fn test (x: i32) {
    let t = thread::spawn({
        // type checking code (never executed but persists in the MIR)
        if false {
            |result : i32| { // We now know the return type of the closure
                #[prusti::spec_only]
                #[prusti::spec_id = "$(NUM_UUID)"]
                #[prusti::assertion = "{/"kind/":{/"Expr/":{/"spec_id/":/"$(UUID)/",/"expr_id/":101}}}"]
                let _thread_ensures = {
                    #[prusti::spec_only]
                    #[prusti::expr_id = "$(NUM_UUID)_101"]
                    || -> bool { result > 0 };
                }
            };
        };
        // return the original closure
        move || -> i32 {
            x = x + 1;
            x
        }
    });
    t.join().unwrap();
}
```

A seperate issue concerning the question of what identifiers are captured by the compiler also appears in the typechecking phase. Consider the code below, in this example, an identifier called y is assigned a value of 1 and then `#[t_ensures(... && y ==1)]` is added. In this case, since y is never captured in the closure, Prusti should report an error ideally at the typechecking stage. However, due to similar reasons with closure return types, this check must be postponed until the compiler complete analysis.

```rust=
fn invalid_t_ensures (x : i32) {
    let y = 1;
    let t: JoinHandle<i32> = thread::spawn(
        #[t_ensures(result > 0 && y == 1)]
        move || {
            x = x + 1
    });
    ...
}
```


The desired design for rewriting specifications for type checking for threads is very similar to how normal pre and postconditions are handled. This involves generating a separate function dedicated to type checking the specifications.

The motivation for this approach is to let the Rust compiler complain when some identifier that is not captured by the closure (for spawning threads) is mentioned in the thread postcondition. (Fig 5a) This behaviour is desired because `y` is never captured so its value might change during the thread's execution so specification should never mention `y`.

##### Fig 5a
```rust=
#[requires(x > 0)]
#[ensures(true)]
fn invalid_t_ensures (x : i32) {
    let y = 1;
    let t: JoinHandle<i32> = thread::spawn(
        #[t_ensures(result > 0 && y == 1)]
        move || {
            x = x + 1
    });
    ...
}
```
The rewritten code would look like the following. Note that the NUM_UUID is the same for lines 3, 5, 6, 9, 13, and 20

##### Fig 5b
```rust=
... // The type checking code for the functions's pre/post conditions are skipped.
#[prusti::spec_only]
#[prusti::spec_id = "$(NUM_UUID)"]
#[prusti::assertion =
  "{/"kind/":{/"Expr/":{/"spec_id/":/"$(UUID)/",/"expr_id/":101}}}"] // this is inaccurate
fn prusti_thread_post_item_invalid_t_ensures_$(NUM_UUID)(x: i32, result: i32) { // we do not know the type of x and result

    #[prusti::spec_only]
    #[prusti::expr_id = "$(NUM_UUID)_101"]
    || -> bool { result > 0 };

    #[prusti::spec_only]
    #[prusti::expr_id = "$(NUM_UUID)_102"]
    || -> bool { y == 1};        // Clearly y is not an argument so rustc will panic
}
// #[prusti::post_spec_id_ref = "$(NUM_UUID)"]  // Refers to the function's pre conditions
// #[prusti::pre_spec_id_ref = "$(NUM_UUID)"]   // Refers to the function's post conditions
fn invalid_t_ensures(x: i32) { 
    let t = thread::spawn(
    	#[prusti::thread_post_spec_id_ref = "$(NUM_UUID)"]
        move || {
        x * 2
    });
    t.join().unwrap();
}
...
```

The main drawback of this strategy is determining the what the arguments are for the type checking function. The only way to get this information is to manually parse the tokenstream which may present all kinds of bugs. 

Additionally, there is a serious flaw in that we are also unable to determine the type of the captured variable. Hence, it may be very difficult to generate the type checking functions with correct argument types.

#### Approach 2
The alternative is to leave the checking of uncaptured identifiers to a later stage. This will happen when we are relating specs to Rust functions. The reason is that at this stage, we have acquired the typing context from the compiler but have yet to start verification. Hence, it is possible to find what identifiers are captured by the following closure from the compiler-generated typing context and raise a panic if thread postcondition contains identifiers not captured. (see [Relating specs to Rust items](###Relating-specs-to-Rust-items))

In this case, it is possible to simply inline the specifications similar to how loop invariants are currently handled. The rewritten code would look like the following. Note that the NUM_UUID on line 8, 9 and 16 are the same 

##### Fig 5c
```rust=
... // The type checking code for the functions's pre/post conditions are skipped.
fn invalid_t_ensures(x: i32) {
    let y = 1;
    let t = thread::spawn({
        // original closure
        let mut closure = move || { x * 2 };
        
        // type checking code (never executed)
        if false {
            let result = closure(); // We call the closure to know its return type
            #[prusti::spec_only]
            #[prusti::spec_id = "$(NUM_UUID)"]
            #[prusti::assertion =
                  "{/"kind/":{/"Expr/":{/"spec_id/":/"$(UUID)/",/"expr_id/":101}}}"] // this is inaccurate
            let _thread_ensures = {
                #[prusti::spec_only]
                #[prusti::expr_id = "$(NUM_UUID)_101"]
                || -> bool { result > 0 };

                #[prusti::spec_only]
                #[prusti::expr_id = "$(NUM_UUID)_102"]
                || -> bool { y == 1};
            }
        };
        
        // return the original closure
        closure
    });
    t.join().unwrap();
}
...
```

#### Return type issue:
A common issue faced by both approaches is that we are unable to determine the return type of the closure when running the procedural macros. Hence, we may run into issues when type checking for the `result`.

One way to work around this is to skip the type checking of results and perform it at a later stage similar to how uncaptured identifiers are treated above in approach 2.

The final way to specify the return type with some Prusti attribute. Then, after the compiler determines the return type of the closure, we can simply check if the two are the same. We might want to do the same thing for uncaptured identifiers. 

The specifcation for thread_postconditions might then look like one of the following:

```rust
#[t_ensures(assertion, return_type, [list_of_captured_identifiers])]
----
// If we are able to determine the captured identifiers
#[t_ensures(assertion, return_type)]
----
// We can also split into two (three) specifications
#[t_ensures(assertion)]
#[t_type(return_type)]
#[t_capture(list_of_captured_identifiers)] // Maybe?
```

### Choice of macros

One of the most interesting Rust features that we are using for parsing is the `proc_macro` crate. In the current solution, the `proc_macro` is unavailable for expression positions (inside functions), which led to the use of `proc_macro_hack` and subsequent adoption of three separate `prusti-contracts*` crate. 

However, it turns out that procedural macros are now supported in expression positions in the rustc 1.45+. With this also comes the ability to use the powerful `#[proc_macro_attribute]`, which allows taking both an attribute and a token. Take for example the following code. In this scenario, the attribute will be the assertion `true` while the token will be the closure `|| { ... }`. This choice will allow us to be able to figure out what identifiers are captured if that information is needed.

```rust
let t = thread::spawn(
    #[t_ensures(true)]
    || {
        ...
    }
)
```

Currently, the following unstable features flags are necessary for proc_macros to work at expression positions with custom attributes:

`#![feature(stmt_expr_attributes)]`  
`#![feature(proc_macro_hygiene)]`

### Relating specs to Rust items

Relating specs to Rust items is one of the main tasks done before Prusti starts verification (encoding into Viper). On a very high level, it involves:
1. Assigning unique IDs to each specification and each expression in a specification's assertion
2. Collecting these specifications after rustc finishes type checking
3. Creating a `specification_map` from the collected specifications
4. which requires the transformation of collected specifications into a representation that implements the `prusti-interface` crate

Note that for specifications, we are mainly talking about pre/postconditions and invariants. Generally, one specification has one assertion which has an arbitrary number of expressions.

In the initial parsing with procedural macros, each specification will generate an unique UUID. This UUID is used all related places, including the name of the type checking function, the `#[prusti::spec_id=...]` label and the prefix for expression IDs. (Expressions are basic units for assertions in the specification). These specification/expression ids are also transformed into a structured JSON format for easier usage later.

Once type checking by the compiler is completed, Prusti will try to assemble the fragmented information. It does this by defining a `SpecCollector` struct which implements the compiler's HIR visitor. This struct will go over the HIR of the code and collect specification items. For expressions, they are added to a `typed_expression` map which is used in the next step for further processing. Furthermore, local id

Finally, when the `SpecCollector` finishes collecting specifications, it will start creating the `SpecificationMap`. The `SpecificationMap` maps `SpecificationID` to `SpecificationSet` and is the central structure created from the the specification parsing and type checking phase. Here, the `SpecificationID` refers to the unique UUID that is generated for specifications during parsing. The `SpecificationSet` refers to a struct that determines the type of specification (precondition etc.) and the `typed_assertion`. This `typed_assertion` is reconstructed from the `typed_expression` mentioned earlier.


## Encoding MIR to Viper (TODO)
This section talks about the design and implementation details for encoding MIR to Viper. It also discusses some interesting/challenging points in the implementation.

### Overview of the workflow (TODO)

### Overview of crates and important files (TODO)

### Encoding strategy

### Applying the correct magic wand at JoinHandle.join()
One question not mentioned in the previous encoding design is how do we know which magic wand to apply when we invoke the join with the JoinHandle. Currently, there are two different approaches to this question. 

For the first approach, we will try to do something similar to how a function's postconditions are handled when the function is called. In other words, the MIR and some of its debug info can be used to relate JoinHandles to threads and directly provide the correct magic wand.

The second approach is to employ some defunctionalization strategy. To clarify, the identifier for the thread that the current JoinHandle is responsible for is carried around. There will be a series of if-else for each thread identifier. (This approach may be redundant and more challenging to work with when spawn and join are not in the same function)


