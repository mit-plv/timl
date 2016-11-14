#!/usr/bin/env ruby

subjects = %w{list lsls tree trivial msort bigO-evolve fold-evolve single-var insertion-sort braun-tree braun-tree-sortedness rbt-sortedness rbt dynamic-table two-stack-queue array-bsearch array-heap array-msort array-msort-inplace array-kmed qsort dijkstra dlist}
descriptions = [
  "Length-indexed lists",
  "Flexibility of \"size\"",
  "Size-indexed binary trees",
  "Trivial examples",
  "Merge sort",
  "Evolving [map] from precise time to big-O time",
  "Evolving [fold] from precise time to big-O time",
  "(TBA)",
  "Insertion sort",
  "Braun trees",
  "Braun trees with invariant for sortedness",
  "Red-black trees with invariant for sortedness",
  "Red-black trees",
  "Dynamic tables with amortized time complexity",
  "Two-stack queues with amortized time complexity",
  "Binary search with arrays",
  "Binary heap with arrays",
  "Merge sort with arrays",
  "In-place merge sort with arrays",
  "k-median search with arrays",
  "Quicksort",
  "Dijkstra algorithm",
  "Double-linked lists"
]

results = subjects.zip(descriptions).map do |(sub, desc)|
  fn = "#{sub}.timl"
  start = Time.new
  system("../main stdlib.pkg #{fn} > /dev/null")
  final = Time.new
  contents = File.open(fn).readlines
  [sub, desc, (final - start).to_s, contents.length.to_s, contents.count { |ln| (ln =~ /absidx|idx|using/) != nil }.to_s]
end

File.open("result.csv", "w") do |f|
  f.puts "Example,Description,Time of type checking (s),#line,#line containing time annotations"
  results.each do |result|
    f.puts result.join(",")
  end
end
