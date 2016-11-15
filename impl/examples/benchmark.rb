#!/usr/bin/env ruby

subjects = %w{list lsls tree msort insertion-sort braun-tree braun-tree-sortedness rbt-sortedness rbt dynamic-table two-stack-queue array-bsearch array-heap array-msort array-msort-inplace array-kmed qsort dijkstra dlist}
descriptions = [
  "List operations",
  "List of lists",
  "Trees",
  "Merge sort",
  "Insertion sort",
  "Braun trees",
  "Braun trees with invariant for sortedness",
  "Red-black trees with invariant for sortedness",
  "Red-black trees",
  "Dynamic tables with amortized time complexity",
  "Two-stack queues with amortized time complexity",
  "Binary search on arrays",
  "Binary heap on arrays",
  "Merge sort on arrays",
  "Inplace merge sort on arrays",
  "k-median search on arrays",
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
  f.puts "Example,Description,Time (s),LOC,LOC containing time annotations"
  results.each do |result|
    f.puts result.join(",")
  end
end
