#!/usr/bin/ruby

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
# John Kerl
# kerl.john.r@gmail.com
# Copyright (c) 2004
# S-box analysis added 2026-10-07
# ================================================================

# Offline S-box analysis:  linear approximation table (LAT), difference
# distribution table (DDT), algebraic normal forms (ANF) of the output
# components, algebraic degrees, and nonlinearity.
#
# Bit-order convention (used uniformly throughout):
# An n-bit vector is the Ruby integer x whose bit i (value 1 << i) holds
# coordinate x_i;  bit position zero is the least significant bit.
# The dot product of masks a and x is parity(popcount(a & x)).
# An ANF monomial for mask m is the product of x_i over the bits set in m.
#
# The S-box is given as an array `table` of length 2**num_in_bits with
# entries in 0 .. 2**num_out_bits - 1.  It need not be a permutation and
# the input and output bit lengths may differ.

require 'Bit_arith.rb'

class Sbox

	# ------------------------------------------------------------
	def initialize(table, num_out_bits = nil)
		num_in = table.length
		if num_in == 0 || (num_in & (num_in - 1)) != 0
			raise "Sbox:  table length must be a power of 2; got #{num_in}."
		end
		@table = table.dup
		@num_in_bits = Bit_arith.exact_log2(num_in)
		max_out = table.max
		if max_out < 0
			raise "Sbox:  table entries must be non-negative."
		end
		inferred = max_out == 0 ? 1 : Bit_arith.msb_pos(max_out) + 1
		@num_out_bits = num_out_bits.nil? ? inferred : num_out_bits
		if @num_out_bits < inferred
			raise "Sbox:  num_out_bits #{@num_out_bits} too small for entry #{max_out}."
		end
	end
	attr_reader :table, :num_in_bits, :num_out_bits

	def num_in
		1 << @num_in_bits
	end
	def num_out
		1 << @num_out_bits
	end

	# ------------------------------------------------------------
	# Dot product of two masks over GF(2):  parity of popcount(a & x).
	def Sbox.dot(a, x)
		Bit_arith.ones(a & x) & 1
	end

	# ------------------------------------------------------------
	# In-place fast Walsh-Hadamard transform of an array of integers,
	# length a power of two.  Butterfly ordering matches the mask
	# convention above:  W[a] = sum_x f[x] * (-1)**(a . x).
	def Sbox.fwht(f)
		n = f.length
		len = 1
		while len < n
			i = 0
			while i < n
				j = i
				while j < i + len
					u = f[j]
					v = f[j + len]
					f[j]     = u + v
					f[j + len] = u - v
					j += 1
				end
				i += 2 * len
			end
			len <<= 1
		end
		f
	end

	# ------------------------------------------------------------
	# In-place Moebius transform over GF(2):  converts a Boolean truth
	# table (entries 0/1) into its ANF coefficient table.  Indexing
	# convention matches fwht:  coefficient at mask m belongs to the
	# monomial formed by the bits set in m.
	def Sbox.mobius(f)
		n = f.length
		len = 1
		while len < n
			i = 0
			while i < n
				j = i
				while j < i + len
					f[j + len] ^= f[j]
					j += 1
				end
				i += 2 * len
			end
			len <<= 1
		end
		f
	end

	# ------------------------------------------------------------
	# Walsh spectrum of the output component selected by mask b:
	#   W[a] = sum_x (-1)**(a.x + b.S(x)),  a in 0 .. num_in-1.
	def walsh_spectrum(b)
		f = Array.new(num_in) { |x| Sbox.dot(b, @table[x]) == 0 ? 1 : -1 }
		Sbox.fwht(f)
	end

	# ------------------------------------------------------------
	# Linear approximation table.  Rows are indexed by input mask a,
	# columns by output mask b;  entry = W_b(a) as above.
	def lat
		cols = (0...num_out).map { |b| walsh_spectrum(b) }
		(0...num_in).map { |a| (0...num_out).map { |b| cols[b][a] } }
	end

	# ------------------------------------------------------------
	# Difference distribution table.  Rows are input differences,
	# columns output differences;  entry counts x with
	# S(x) ^ S(x ^ dx) == dy.  Every row sums to num_in.
	def ddt
		t = Array.new(num_in) { Array.new(num_out, 0) }
		(0...num_in).each do |x|
			(0...num_in).each do |dx|
				t[dx][@table[x] ^ @table[x ^ dx]] += 1
			end
		end
		t
	end

	# Differential uniformity:  largest DDT entry off the dx == 0 row.
	def differential_uniformity
		t = ddt
		(1...num_in).map { |dx| t[dx].max }.max
	end

	# ------------------------------------------------------------
	# ANF coefficient table of output bit `bit` (bit 0 = LSB of S(x)).
	# Entry at mask m is the coefficient of the monomial for m.
	def anf(bit)
		if bit < 0 || bit >= @num_out_bits
			raise "Sbox.anf:  bit #{bit} out of range 0..#{@num_out_bits - 1}."
		end
		Sbox.mobius(Array.new(num_in) { |x| (@table[x] >> bit) & 1 })
	end

	# Algebraic degree of output bit `bit`;  -1 for the zero function.
	def algebraic_degree_of(bit)
		coeffs = anf(bit)
		deg = -1
		(0...num_in).each do |m|
			if coeffs[m] == 1
				w = Bit_arith.ones(m)
				deg = w if w > deg
			end
		end
		deg
	end

	# Algebraic degree of the S-box:  max over output bits.
	def algebraic_degree
		(0...@num_out_bits).map { |bit| algebraic_degree_of(bit) }.max
	end

	# ------------------------------------------------------------
	# Nonlinearity of the component selected by mask b (b != 0):
	#   2**(n-1) - (1/2) * max_a |W_b(a)|.
	def component_nonlinearity(b)
		w = walsh_spectrum(b)
		(num_in >> 1) - (w.map { |v| v.abs }.max >> 1)
	end

	# Nonlinearity of the S-box:  minimum over nonzero output masks.
	def nonlinearity
		(1...num_out).map { |b| component_nonlinearity(b) }.min
	end

	# ------------------------------------------------------------
	# Parseval:  for every output mask b, sum_a W_b(a)**2 == num_in**2.
	def parseval_ok?
		(0...num_out).all? do |b|
			walsh_spectrum(b).inject(0) { |s, v| s + v * v } == num_in * num_in
		end
	end

	# Every DDT row sums to num_in.
	def ddt_row_sums_ok?
		ddt.all? { |row| row.inject(:+) == num_in }
	end

	# ------------------------------------------------------------
	# Human-readable ANF, e.g. "1 + x0 + x0*x2".
	def anf_to_s(bit)
		coeffs = anf(bit)
		terms = []
		(0...num_in).each do |m|
			next if coeffs[m] == 0
			if m == 0
				terms << "1"
			else
				factors = []
				(0...@num_in_bits).each do |i|
					factors << "x#{i}" if (m >> i) & 1 == 1
				end
				terms << factors.join("*")
			end
		end
		terms.empty? ? "0" : terms.join(" + ")
	end

	# ------------------------------------------------------------
	def to_s
		rows = (0...num_in).map { |x| "  %0#{@num_in_bits}b -> %0#{@num_out_bits}b" % [x, @table[x]] }
		"S-box (#{@num_in_bits} -> #{@num_out_bits} bits):\n" + rows.join("\n")
	end

	# ------------------------------------------------------------
	# Offline report for this S-box.
	def report(name = "S")
		lat_t = lat
		ddt_t = ddt
		lines = []
		lines << "=============================================================="
		lines << "S-box #{name}:  #{@num_in_bits} input bits, #{@num_out_bits} output bits"
		lines << "table: [#{@table.join(', ')}]"
		lines << "bit order: bit 0 = LSB; masks a.x = parity(popcount(a & x))"
		lines << ""
		lines << "LAT (rows = input mask a, columns = output mask b):"
		lines << Sbox.table_to_s(lat_t)
		lines << ""
		lines << "DDT (rows = input difference, columns = output difference):"
		lines << Sbox.table_to_s(ddt_t)
		lines << ""
		lines << "differential uniformity: #{differential_uniformity}"
		lines << "DDT row sums == #{num_in}: #{ddt_row_sums_ok?}"
		lines << "Parseval sum_a W_b(a)^2 == #{num_in * num_in}: #{parseval_ok?}"
		lines << ""
		lines << "output component ANFs and degrees:"
		(0...@num_out_bits).each do |bit|
			lines << "  y#{bit} = #{anf_to_s(bit)}   (degree #{algebraic_degree_of(bit)})"
		end
		lines << "algebraic degree: #{algebraic_degree}"
		lines << "nonlinearity: #{nonlinearity}"
		lines.join("\n") + "\n"
	end

	# ------------------------------------------------------------
	def Sbox.table_to_s(t)
		width = t.flatten.map { |v| v.to_s.length }.max
		t.map { |row| "  " + row.map { |v| v.to_s.rjust(width) }.join(" ") }.join("\n")
	end

	# Combined offline report for several named S-boxes:
	#   Sbox.report_all([["id3", s1], ["present", s2]])
	def Sbox.report_all(named_sboxes)
		named_sboxes.map { |name, sbox| sbox.report(name) }.join("\n")
	end

end
