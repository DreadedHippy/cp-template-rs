use std::{cell::RefCell, clone, cmp::{min, Ordering, Reverse}, collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque}, fmt::{format, Binary}, hash::Hash, i64, io::Cursor, mem::swap, ops::{Add, AddAssign}, rc::Rc, result, usize};
use std::ops::Bound::{Included, Excluded};

#[allow(unused)]
macro_rules! cina {
    ($t:tt) => {{
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).expect("fail");
        temp.split_whitespace()
            .map(|x| x.parse::<$t>().unwrap())
            .collect::<Vec<$t>>()
    }};
}


macro_rules! cin {
    ($t:tt) => {{
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).expect("fail");
        temp.trim().parse::<$t>().unwrap()
    }};
}

#[allow(unused)]
macro_rules! cins {
    () => {{
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).expect("fail");
        temp.trim().to_string()
    }};
}

#[allow(unused)]
macro_rules! read_joined_chars {
    ($t:tt) => {{
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).expect("fail");
        temp.trim().chars()
        .collect::<Vec<$t>>()
    }};
}

#[allow(unused)]
macro_rules! tuple {
    [$xs:expr; 2] => {
        { let value = $xs; (value[0], value[1]) }
    };
    [$xs:expr; 3] => {
        { let value = $xs; (value[0], value[1], value[2]) }
    };
    [$xs:expr; 4] => {
        { let value = $xs; (value[0], value[1], value[2], value[3]) }
    };
    [$xs:expr; $t:ty ;2] => {
        { let value = $xs; (value[0] as $t, value[1] as $t) }
    };
    [$xs:expr; $t:ty; 3] => {
        { let value = $xs; (value[0] as $t, value[1] as $t, value[2] as $t) }
    };
    [$xs:expr; $t:ty; 4] => {
        { let value = $xs; (value[0] as $t, value[1] as $t, value[2] as $t, value[3] as $t) }
    };
}

type U = usize;
type I = isize;
type F = f64;

//*! PRE-COMPUTATION
//*! CAPACITY ERRORS
//*! USING `RETURN` INSTEAD OF `CONTINUE`
//*! NOT PROPERLY TESTING EDGE-CASES
//*! NOT READING DOCUMENTATION OF STD TOOLS PROPERLY E.G BTREESET::RANGE() PANIC CONDITIONS
//*! BINARY SEARCH ON SUBSTRING PROBLEMS
//*! NEIGHBORING NUMBERS: EXPAND/SHRINK INTERVAL WINDOW */
//*! BITMASKING: FORM YOUR TRUTH TABLES, USE U64
//*! THINK SIMPLY !!!

const MODULO: i64 = 1_000_000_007;

fn main() {
    let (n, k) = tuple!(cina!(usize); 2);
    let mut graph = vec![HashSet::new(); n + 1];

    for _ in 1..n {
        let (a, b) = tuple!(cina!(usize); 2);

        graph[a].insert(b);
        graph[b].insert(a);
    }

    solve(n, k, graph);



}

fn solve(n: usize, k: usize, graph: Vec<HashSet<usize>>) {
    let mut path = HashSet::new();
    let mut paths = vec![(0, HashSet::new(), 0); n + 1];
    let mut visited = HashSet::new();

    to_capital(1, &graph, &mut visited, &mut path, &mut paths);

    // let mut paths = paths.into_iter().enumerate().collect::<Vec<_>>();

    paths.sort_unstable_by(|a, b| {
        b.2.cmp(&a.2).reverse().then_with(|| b.1.len().cmp(&a.1.len()))
    });

    let ind = paths.iter().skip(1).map(|&(x, _, _)| x).take(k).collect::<HashSet<_>>();
    
    let mut h = 0;
    for i in 1..=n {
        let c = paths[i].0;
        let l = paths[i].1.len();
        if !ind.contains(&c) {continue;}

        h += l - paths[i].1.intersection(&ind).count();


    }

    // println!("{:?}", paths);
    println!("{}", h);
}

fn to_capital(node: usize, graph: &Vec<HashSet<usize>>, visited: &mut HashSet<usize>, path: &mut HashSet<usize>, paths: &mut Vec<(usize, HashSet<usize>, usize)> ) {
    path.insert(node);
    visited.insert(node);

    for &child in &graph[node] {
        if visited.contains(&child) {continue;}

        to_capital(child, graph, visited, path, paths);
    }

    paths[node] = (node, path.clone(), graph[node].len());
    path.remove(&node);
}


fn ktree(n: u128, k: u128, d: u128, sum: u128, df: bool, map: &mut HashMap<(u128, bool), u128>) -> u128 {
    if map.get(&(n - sum, df)).is_some() {
        let e = *map.get(&(n-sum, df)).unwrap();

        return e;
    }
    
    let mut count = 0;

    for i in 1..=k {
        let sum = sum + i;
        let df = df || i >= d;

        if sum > n {break}

        if sum == n && df{
            count += 1;
            break;
        }

        count += ktree(n, k, d, sum, df, map);
        count %= MODULO as u128;
    }

        map.insert((n - sum, df), count);

    return count;
}

fn bin_search(mut l: usize, mut r: usize, f: impl Fn(usize) -> bool) -> (usize, usize) {
    while r > l + 1 {
        let mid = (r + l) / 2;
        if f(mid) {
            r = mid;
        } else {
            l = mid;
        }
    }
    (l, r)
}

fn vec_to_string<T: ToString>(a: &Vec<T>) -> String {
    a.iter().map(|x| x.to_string() + " ").collect::<String>().trim().to_string()
}

pub fn prime_factorization(mut number:i128) -> BTreeMap<i128, i128> {
    let mut prime_factors: BTreeMap<i128, i128> = BTreeMap::new();

    // Step 1 : Divide by 2
    let mut freq:i128 = 0;

    // You can use number % 2 == 0 also,
    // but this method is much more efficient
    while number&1 == 0 {
        number >>=1;
        // Again, You can use number /= 2 also,
        // but this is much more efficient
        freq+=1;
    }

    if freq > 0 {
        prime_factors.insert(2, freq);
    }

    // Step 2 : start from 3, and go till square root of number
    let mut i = 3;
    while i*i <= number {

        // Step 3 : Check if i is factor of number
        if number%i==0 {
            freq = 0;
            while number%i==0 {
                number/=i;
                freq+=1;
            }
            prime_factors.insert(i, freq);
        }
        i+=2;
    }

    // Step 4 : Check if number become 1 or not
    if number > 1 {
        prime_factors.insert(number, 1);
    }

    return prime_factors;
}

// pub fn petr(rotations: &Vec<usize>, )

// pub fn knapsack(w: usize, weights: Vec<usize>, profits: Vec<usize>, position: usize) {
//     // position = index + 1;
//     if position == 0 || W == 0{
//         return 0
//     }

//     if weights[position - 1] > W {
//         // if weight > knapsack capacity, skip
//         return knapsack(w, weights, profits, position - 1);
//     }
// }

fn isqrt(n: usize) -> usize {
    n == 0 && return n;
    let mut s = (n as f64).sqrt() as usize;
    s = (s + n / s) >> 1;
    if s * s > n { s - 1 } else { s }
}

fn perfect_sqrt(n: usize) -> isize {
    match n & 0xf {
        0 | 1 | 4 | 9 => {
            let t = isqrt(n);
            if t*t == n { t as isize } else { -1 }
        },
        _ => -1,
    }
}

fn is_prime(n:usize) -> bool{

    // Iterate from i = 2 to sqrt ( n )
    if n < 2 {
        return false
    }
    if n == 2 {
        return true
    }

    let mut i:usize = 2;
    while i*i<=n {
        // Return false if the number is divisible
        if n%i == 0 {
            return false;
        }
        i+=1;
    }

    // Return true finally
    return true;
}


pub fn lcm(n1: u64, n2: u64) -> u64 {
    let (mut x, mut y, mut rem) = (0, 0, 0);
    if (n1 > n2) {
        x = n1;
        y = n2;
    }
    else {
        x = n2;
        y = n1;
    }

    rem = x % y;

    while (rem != 0) {
        x = y;
        y = rem;
        rem = x % y;
    }

    n1 * n2 / y
}

pub fn gcd(mut u: u64, mut v: u64) -> u64 {
    // Base cases: gcd(n, 0) = gcd(0, n) = n
    if u == 0 {
        return v;
    } else if v == 0 {
        return u;
    }

    // Using identities 2 and 3:
    // gcd(2ⁱ u, 2ʲ v) = 2ᵏ gcd(u, v) with u, v odd and k = min(i, j)
    // 2ᵏ is the greatest power of two that divides both 2ⁱ u and 2ʲ v
    let i = u.trailing_zeros();  u >>= i;
    let j = v.trailing_zeros();  v >>= j;
    let k = min(i, j);

    loop {
        // u and v are odd at the start of the loop
        // debug_assert!(u % 2 == 1, "u = {} should be odd", u);
        // debug_assert!(v % 2 == 1, "v = {} should be odd", v);

        // Swap if necessary so u ≤ v
        if u > v {
            swap(&mut u, &mut v);
        }

        // Identity 4: gcd(u, v) = gcd(u, v-u) as u ≤ v and u, v are both odd 
        v -= u;
        // v is now even

        if v == 0 {
            // Identity 1: gcd(u, 0) = u
            // The shift by k is necessary to add back the 2ᵏ factor that was removed before the loop
            return u << k;
        }

        // Identity 3: gcd(u, 2ʲ v) = gcd(u, v) as u is odd
        v >>= v.trailing_zeros();
    }
}

pub fn modulo_non_zero(number: usize, base: usize) -> usize {
    match number % base {
        0 => base,
        k => k
    }
}

pub fn max_sub_array(nums: Vec<i64>) -> (i64, usize) {
    use std::cmp;
    
    let (mut curr_sum, mut global_sum) = (0, i64::MIN);
    let mut end_index = 0;
    
    for i in 0..nums.len() {
        curr_sum+= nums[i];
        let old = global_sum;
        global_sum = cmp::max(curr_sum, global_sum);
        if global_sum > old {
            end_index = i
        }
        
        if curr_sum < 0 {
            curr_sum = 0;
        }            
    }
    
    (global_sum, end_index)
}

fn get_factors_functional(n: u64) -> Vec<u64> {
    (1..).take_while(|&x| x * x <= n).into_iter().filter(|&x| n % x == 0).flat_map(|x| if x == n/x {vec![x]} else {vec![x, n/x]}).collect::<Vec<u64>>()
}

// BITWISE OPERATIONS;
pub fn get_msb(n: u32) -> u32{
	32 - (n.leading_zeros() - 1)
}