#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
# Binary Reed-Muller codes RM(r, m) over GF(2), built on top of
# Bit_vector and Bit_matrix.
#
# Conventions (public, so codewords can be checked independently):
#
# * Variables are x_0, x_1, ..., x_{m-1} (see #variables).
# * Evaluation points are all of GF(2)^m, indexed j = 0 .. 2^m-1.
#   Point j is the m-bit vector whose i-th coordinate x_i is bit i
#   of j (bit 0 = LSB).  See #eval_points and #eval_point_bits.
# * Codeword position j holds the evaluation at point j.
# * Monomials (rows of the generator matrix, and hence info-bit
#   positions) are all squarefree monomials of degree <= r, ordered
#   by increasing degree, ties broken lexicographically on the
#   variable-index set.  See #monomials.
#
# Decoding is Reed's majority-logic algorithm: coefficients are
# recovered from highest degree down, each by a majority vote over
# 2^(m-s) disjoint checksums (s = degree of the monomial).  It runs
# in time polynomial in n = 2^m and never enumerates the 2^k info
# words.  Correction of up to t = floor((dmin-1)/2) errors is
# guaranteed; beyond that the decoder returns its best candidate
# together with its distance to the received word and an honest
# guaranteed=false flag.
# ================================================================

require 'Bit_matrix.rb'
require 'Bit_vector.rb'

class RM_code

	# ------------------------------------------------------------
	def initialize(r, m)
		if (r < 0) || (m < 1) || (r > m)
			raise "RM_code:  need 0 <= r <= m, m >= 1; got r=#{r}, m=#{m}."
		end
		@r = r
		@m = m
		@n = 1 << m               # block length
		@dmin = 1 << (m - r)      # minimum distance
		@t = (@dmin - 1) >> 1     # guaranteed correction radius

		# Evaluation points, in codeword-position order.
		@eval_points = (0...@n).to_a

		# Monomials as variable-index sets, in info-bit order.
		@monomials = []
		for deg in 0..r
			(0...m).to_a.combination(deg) do |vars|
				@monomials.push(vars)
			end
		end
		@k = @monomials.size      # number of info bits

		# Bitmask of each monomial's variable set, for fast evaluation:
		# monomial S evaluates at point j to 1 iff (j & mask) == mask.
		@monomial_masks = @monomials.map do |vars|
			vars.inject(0) { |mask, i| mask | (1 << i) }
		end

		@generator = Bit_matrix.new(@k, @n)
		for row in 0...@k
			mask = @monomial_masks[row]
			bits = 0
			for j in 0...@n
				bits |= (1 << j) if (j & mask) == mask
			end
			@generator.rows[row].bits = bits
		end
	end

	attr_reader :r, :m, :n, :k, :dmin, :t
	attr_reader :variables, :eval_points, :monomials, :monomial_masks
	attr_reader :generator

	# ------------------------------------------------------------
	# Variable names, in coordinate order.
	def variables
		(0...@m).map { |i| "x#{i}" }
	end

	# Coordinates of evaluation point j as [x_0, x_1, ..., x_{m-1}].
	def eval_point_bits(j)
		if (j < 0) || (j >= @n)
			raise "RM_code:  point index #{j} out of bounds 0..#{@n-1}"
		end
		(0...@m).map { |i| (j >> i) & 1 }
	end

	# Human-readable monomial names, in info-bit order.
	def monomial_strings
		@monomials.map do |vars|
			vars.empty? ? "1" : vars.map { |i| "x#{i}" }.join("*")
		end
	end

	def to_s
		"RM(#{@r},#{@m}): n=#{@n} k=#{@k} dmin=#{@dmin} t=#{@t}"
	end

	# ------------------------------------------------------------
	# info: Bit_vector of length k (info-bit order = #monomials order).
	# Returns a Bit_vector of length n (position j = value at point j).
	def encode(info)
		if info.num_bits != @k
			raise "RM_code:  info word must have #{@k} bits; got #{info.num_bits}."
		end
		bits = 0
		for i in 0...@k
			bits ^= @generator.rows[i].bits if info[i] == 1
		end
		codeword = Bit_vector.new(@n)
		codeword.bits = bits
		codeword
	end

	# ------------------------------------------------------------
	# Reed majority-logic decoding.  received: Bit_vector of length n.
	# Returns an RM_decode_result; see below.  Never enumerates info
	# words: cost is O(k * n * 2^r) bit operations.
	def decode(received)
		if received.num_bits != @n
			raise "RM_code:  received word must have #{@n} bits; got #{received.num_bits}."
		end
		remaining = received.bits
		coeffs = Array.new(@k, 0)
		ties = 0

		# Highest-degree coefficients first: after subtracting all
		# monomials T strictly containing S (all of higher degree,
		# hence already decoded), the checksum of the remaining word
		# over the subcube {x_i free for i in S, others fixed} equals
		# the coefficient of S.
		order = (0...@k).sort_by { |i| -@monomials[i].length }
		for i in order
			mask = @monomial_masks[i]
			ones = 0
			total = 0
			b = 0
			while b < @n
				if (b & mask) == 0
					# Checksum over the subcube b + span(S).
					parity = 0
					a = mask
					while true
						parity ^= (remaining >> (b | a)) & 1
						break if a == 0
						a = (a - 1) & mask
					end
					ones += parity
					total += 1
				end
				b += 1
			end
			if ones * 2 > total
				bit = 1
			elsif ones * 2 < total
				bit = 0
			else
				bit = 0 # tied vote: arbitrary, and flagged below
				ties += 1
			end
			coeffs[i] = bit
			remaining ^= @generator.rows[i].bits if bit == 1
		end

		info = Bit_vector.new(@k)
		for i in 0...@k
			info[i] = coeffs[i]
		end
		codeword = encode(info)
		distance = RM_code.hamming_int(codeword.bits ^ received.bits)
		# Within the correction radius the decoded codeword is the
		# unique closest codeword, so recovery is guaranteed.  Beyond
		# it we report the candidate and its distance, nothing more.
		guaranteed = (2 * distance < @dmin)
		RM_decode_result.new(info, codeword, distance, guaranteed, ties)
	end

	# ------------------------------------------------------------
	def RM_code.hamming_int(x)
		count = 0
		while x != 0
			x &= x - 1
			count += 1
		end
		count
	end

end

# ================================================================
# Result of RM_code#decode.
#
# * info, codeword: the decoder's candidate (Bit_vector).
# * distance:       Hamming distance from codeword to the received word.
# * guaranteed:     true iff distance is within the correction radius
#                   t = floor((dmin-1)/2), i.e. recovery of the
#                   transmitted word is provably correct (assuming at
#                   most t errors occurred).  Never claimed otherwise.
# * ties:           number of majority votes that came out tied
#                   (only possible beyond the correction radius).
# ================================================================
class RM_decode_result
	def initialize(info, codeword, distance, guaranteed, ties)
		@info = info
		@codeword = codeword
		@distance = distance
		@guaranteed = guaranteed
		@ties = ties
	end
	attr_reader :info, :codeword, :distance, :guaranteed, :ties

	def to_s
		"info=#{info} distance=#{distance} " \
			"guaranteed=#{guaranteed} ties=#{ties}"
	end
end
