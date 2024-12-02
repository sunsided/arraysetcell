#![no_main]
use arraysetcell::ArraySetCell;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if data.is_empty() {
        return;
    }

    // Determine capacity based on the input length
    let capacity = (data[0] as usize % 32) + 1; // Dynamic capacity: 1 to 32
    let mut array = ArraySetCell::<u8, 32>::new();

    for &value in data.iter().skip(1).take(capacity) {
        if array.is_full() {
            break;
        }
        array.push(value);
    }

    while !array.is_empty() {
        array.pop();
    }
});
