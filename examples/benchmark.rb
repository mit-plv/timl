#!/usr/bin/env ruby

template = 
%q{
list & List operations & 0.171 & 26 & 4 & $n$, $mn$ \\\\
ragged-matrix & List of lists & 0.113 & 14 & 1 & $m^2 n$ \\\\
tree & Trees & 0.222 & 112 & 15 & $mn$\\\\
msort & Merge sort & 0.286 & 63 & 14 & $mn\log n$ \\\\
insertion-sort & Insertion sort & 0.15 & 22 & 4 & $mn^2$ \\\\
braun-tree & Braun trees & 0.225 & 87 & 11 & $\log n$, $\log^2 n$ \\\\
rbt & Red-black trees & 0.533 & 328 & 18 & $\log n$ \\\\
dynamic-table & Dynamic tables & 0.145 & 116 & 10 & (amortized) $1$ \\\\
functional-queue & Two-stack queues & 0.15 & 95 & 7 & (amortized) $1$ \\\\
array-bsearch & Binary search & 0.169 & 42 & 2 & $m\log n$ \\\\
array-heap & Binary heap & 0.241 & 138 & 6 & $m\log n$ \\\\
array-msort & Merge sort on arrays & 0.243 & 109 & 7 & $mn\log n$ \\\\
array-msort-inplace & In-place merge sort on arrays & 0.293 & 132 & 9 & $mn\log n$ \\\\
array-kmed & k-median search & 0.152 & 69 & 8 & $mn^2$ \\\\
dlist & Doubly linked lists & 0.305 & 111 & 10 & $mn$\\\\
qsort & Quicksort & 0.121 & 39 & 7 & $m n^2$ \\\\
dijkstra & Dijkstra's & 0.125 & 74 & 0 & $(m_++m_\leq)n^2$ \\\\
}

template = template.split("\n").join("")

lines = template.split(%q{\\\\})

lines = lines.map do |line|
  line.split('&').map do |x| x.strip end
end

subjects = lines.map do |x| x[0] end
descriptions = lines.map do |x| x[1] end
coms = lines.map do |x| x[5] end

results = subjects.zip(descriptions).map do |(sub, desc)|
  fn = "#{sub}.timl"
  start = Time.new
  system("../main stdlib.pkg #{fn} > /dev/null")
  final = Time.new
  contents = File.open(fn).readlines
  [sub, desc, (final - start).round(3).to_s, contents.length.to_s, contents.count { |ln| (ln =~ /absidx|idx|using/) != nil }.to_s]
end

File.open("result.csv", "w") do |f|
  f.puts "Example,Description,Time (s),LOC,LOC containing time annotations"
  results.each do |result|
    f.puts result.join(",")
  end
end

puts
results.zip(coms).each do |(line, com)|
  line = line << com
  line = line.join(" & ")
  line = line + " \\\\"
  puts line
end
puts
