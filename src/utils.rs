use std::collections::HashSet;


fn get_factors(num: usize) -> Vec<i64>{
	let root = f64::sqrt(num as f64) as i64 + 1;

	let mut result = HashSet::with_capacity(root as usize);

	for i in 1..=root {
			if num % i as usize == 0 {
					result.insert(i);
					result.insert(num as i64/i);
			}
			// println!("{:?}",result);
	}

	let r = result.into_iter().collect();
	r

}


fn format_radix(mut x: u32, radix: u32) -> String {
	let mut result = vec![];

	loop {
			let m = x % radix;
			x = x / radix;


			// will panic if you use a bad radix (< 2 or > 36).
			result.push(std::char::from_digit(m, radix).unwrap());
			if x == 0 {
					break;
			}
	}
	result.into_iter().rev().collect()
}


fn sort_vecdeque<T: Ord>(x: &mut VecDeque<T>) {
	x.rotate_right(x.as_slices().1.len());
	assert!(x.as_slices().1.is_empty());
	x.as_mut_slices().0.sort();
}


pub fn get_msb(n: u32) -> u32{
	32 - (n.leading_zeros() - 1)
}

//! BINARY SEARCH

fn binary_search() {	
	let (a, b) = (info[0], info[1]);
	
	let d = b-a;
	
	// let lim = 2*d;
	
	let (mut l, mut r) = (0, d);
	
	let mut mid = (r - l)/2;

	while l <= r {
		let calc = (mid*(mid+1))/2;

		if calc > d {
			r = mid -1;
		} else if calc < d {
			l = mid +1;
		} else {
			break
		}
			
			
		mid = (r+l)/2;
	}
		
	println!("{}", mid + 1);
		
}