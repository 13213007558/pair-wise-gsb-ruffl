#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
# S-box nonlinearity metrics for offline algorithm analysis:
# linear approximation table, difference distribution table,
# algebraic normal forms, algebraic degree, and nonlinearity.
#
# Bit-order convention (uniform throughout, matching Bit_vector):
# an n-bit vector is stored as a Ruby integer with bit 0 = LSB
# (appearing rightmost when printed).  Input/output masks a, b and
# the inner product a.x = parity(a & x) all use this convention.
#
# No external cryptographic tools are used; the linear approximation
# table is computed with the fast Walsh-Hadamard transform and the
# algebraic normal forms with the fast Moebius transform.
# ================================================================

class S_box

	# ------------------------------------------------------------
	# table: array of 2**num_input_bits integers, each in 0 ... 2**num_output_bits - 1.
	# num_output_bits is inferred from the largest table entry unless given.
	def initialize(table, num_output_bits = nil)
		n = table.length
		if n < 2 || (n & (n - 1)) != 0
			raise "S_box: table size must be a power of two >= 2; got #{n}."
		end
		@num_input_bits = Math.log2(n).to_i
		if num_output_bits.nil?
			max_entry = table.max
			num_output_bits = max_entry == 0 ? 1 : max_entry.bit_length
		end
		if num_output_bits < 1
			raise "S_box: num_output_bits must be >= 1; got #{num_output_bits}."
		end
		table.each do |e|
			if !e.is_a?(Integer) || e < 0 || e >= (1 << num_output_bits)
				raise "S_box: entry #{e} out of range 0..#{(1 << num_output_bits) - 1}."
			end
		end
		@table = table.dup
		@num_output_bits = num_output_bits
	end
	attr_reader :num_input_bits, :num_output_bits, :table

	# ------------------------------------------------------------
	# Parity of the inner product a.x under the LSB-first convention.
	def S_box.inner_product(a, x)
		(a & x).to_s(2).count('1') & 1
	end

	# ------------------------------------------------------------
	# In-place fast Walsh-Hadamard transform (butterfly, no scaling).
	# Input: array of 2**k numbers.  Output: W[a] = sum_x f(x) * (-1)^(a.x).
	def S_box.fast_walsh_transform(f)
		size = f.length
		h = 1
		while h < size
			i = 0
			while i < size
				j = i
				while j < i + h
					u = f[j]
					v = f[j + h]
					f[j]     = u + v
					f[j + h] = u - v
					j += 1
				end
				i += 2 * h
			end
			h *= 2
		end
		f
	end

	# ------------------------------------------------------------
	# In-place fast Moebius transform over GF(2).
	# Maps a truth table f[x] to ANF coefficients c[u] with
	# f(x) = XOR over u of c[u] * x^u (x^u = product of x_i for bits i of u).
	def S_box.mobius_transform(f)
		size = f.length
		h = 1
		while h < size
			i = 0
			while i < size
				j = i
				while j < i + h
					f[j + h] ^= f[j]
					j += 1
				end
				i += 2 * h
			end
			h *= 2
		end
		f
	end

	# ------------------------------------------------------------
	# LAT[a][b] = sum_x (-1)^(a.x + b.S(x)), computed row-wise (one FWT
	# per output mask b) and stored indexed [input mask a][output mask b].
	def lat
		if @lat.nil?
			n = @num_input_bits
			size = 1 << n
			m = @num_output_bits
			@lat = Array.new(size) { Array.new(1 << m, 0) }
			(0 ... (1 << m)).each do |b|
				signs = Array.new(size)
				(0 ... size).each do |x|
					signs[x] = S_box.inner_product(b, @table[x]) == 0 ? 1 : -1
				end
				w = S_box.fast_walsh_transform(signs)
				(0 ... size).each do |a|
					@lat[a][b] = w[a]
				end
			end
		end
		@lat
	end

	# ------------------------------------------------------------
	# DDT[a][b] = #{x : S(x) ^ S(x^a) = b}.  Every row sums to 2**n.
	def ddt
		if @ddt.nil?
			size = 1 << @num_input_bits
			@ddt = Array.new(size) { Array.new(1 << @num_output_bits, 0) }
			(0 ... size).each do |a|
				(0 ... size).each do |x|
					@ddt[a][@table[x] ^ @table[x ^ a]] += 1
				end
			end
		end
		@ddt
	end

	# ------------------------------------------------------------
	# ANF coefficient array for output bit j (bit 0 = LSB of S(x)),
	# via the Moebius transform of that component's truth table.
	def anf(j)
		if j < 0 || j >= @num_output_bits
			raise "S_box: output bit #{j} out of bounds 0..#{@num_output_bits - 1}."
		end
		truth = @table.map { |y| (y >> j) & 1 }
		S_box.mobius_transform(truth)
	end

	# ------------------------------------------------------------
	# Algebraic degree of output bit j: highest Hamming weight of any
	# monomial with a nonzero ANF coefficient.  The zero function has
	# degree -1 by convention.
	def algebraic_degree(j)
		degree = -1
		anf(j).each_with_index do |c, u|
			if c == 1
				weight = u.to_s(2).count('1')
				degree = weight if weight > degree
			end
		end
		degree
	end

	# Highest algebraic degree over all output components.
	def algebraic_degree_all
		(0 ... @num_output_bits).map { |j| algebraic_degree(j) }.max
	end

	# ------------------------------------------------------------
	# Largest |LAT[a][b]| over all a and all nonzero output masks b.
	def max_lat_entry
		best = 0
		size = 1 << @num_input_bits
		(1 ... (1 << @num_output_bits)).each do |b|
			(0 ... size).each do |a|
				v = lat[a][b].abs
				best = v if v > best
			end
		end
		best
	end

	# ------------------------------------------------------------
	# Nonlinearity: min over nonzero b and all a of the Hamming distance
	# between the Boolean function x -> b.S(x) and the affine function
	# x -> a.x (+ const).  Equals 2^(n-1) - max|LAT[a][b]|/2 for b != 0.
	def nonlinearity
		(1 << (@num_input_bits - 1)) - max_lat_entry / 2
	end

	# ------------------------------------------------------------
	# Single offline report with all nonlinearity metrics.
	def report
		n = @num_input_bits
		m = @num_output_bits
		size = 1 << n
		lines = []
		lines << "S-box: #{n} input bits, #{m} output bits"
		lines << "Table: [#{@table.join(', ')}]"
		lines << "Bit-order convention: bit 0 = LSB (rightmost); masks and inner products use the same convention."
		lines << ""
		lines << "Linear approximation table LAT[a][b] = sum_x (-1)^(a.x + b.S(x))"
		lines << "(rows a = input mask, columns b = output mask)"
		header = "      " + (0 ... (1 << m)).map { |b| "%6d" % b }.join
		lines << header
		(0 ... size).each do |a|
			lines << ("%4d  " % a) + (0 ... (1 << m)).map { |b| "%6d" % lat[a][b] }.join
		end
		lines << ""
		lines << 'Difference distribution table DDT[a][b] = #{x : S(x) ^ S(x^a) = b}'
		lines << "(rows a = input difference, columns b = output difference; each row sums to #{size})"
		lines << header
		(0 ... size).each do |a|
			lines << ("%4d  " % a) + (0 ... (1 << m)).map { |b| "%6d" % ddt[a][b] }.join
		end
		lines << ""
		lines << "Algebraic normal forms of output components (Moebius transform; x0 = LSB):"
		(0 ... m).each do |j|
			lines << "  y#{j} = #{S_box.anf_to_s(anf(j), n)}"
			lines << "  algebraic degree of y#{j}: #{algebraic_degree(j)}"
		end
		lines << "Algebraic degree (max over components): #{algebraic_degree_all}"
		lines << ""
		lines << "Max |LAT[a][b]| over b != 0: #{max_lat_entry}"
		lines << "Nonlinearity (2^(n-1) - max|LAT|/2 over b != 0): #{nonlinearity}"
		lines.join("\n") + "\n"
	end

	# ------------------------------------------------------------
	# Human-readable ANF, e.g. "1 ^ x0 ^ x1*x2".  Bit i of monomial
	# index u selects variable xi (x0 = LSB).
	def S_box.anf_to_s(coeffs, num_variables)
		terms = []
		coeffs.each_with_index do |c, u|
			next if c == 0
			if u == 0
				terms << "1"
			else
				factors = []
				(0 ... num_variables).each do |i|
					factors << "x#{i}" if (u >> i) & 1 == 1
				end
				terms << factors.join("*")
			end
		end
		terms.empty? ? "0" : terms.join(" ^ ")
	end

end
