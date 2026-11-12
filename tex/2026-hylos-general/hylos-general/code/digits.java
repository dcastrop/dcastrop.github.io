// Left to right: the obvious loop
long n = 0;
for (int d : digits) n = 10 * n + d;

// In parallel: Java also asks for a combiner
record Num(long val, long scale) {}              // scale: 10 to the #digits
Num r = digits.parallelStream().reduce(
    new Num(0, 1),
    (a, d) -> new Num(10 * a.val() + d, 10 * a.scale()),    // accumulator
    (a, b) -> new Num(a.val() * b.scale() + b.val(),          // combiner
                      a.scale() * b.scale()));
