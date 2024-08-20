import Std.Tactic.BVDecide

open Lean

/-
The benchmarks are binary and trees with 2^n variables where n increases each line
-/

-- Our benchmark terms are huge, no need to waste time on linting
set_option linter.all false

-- All of these are ~subsecond
theorem t1 (_ : x = true) (x1 : Bool) (x0 : Bool) (_ : (x0 && x1) = x) : x0 = true := by bv_decide
theorem t2 (_ : x = true) (x1 : Bool) (x0 : Bool) (_ : (x0 && x1) = x) (x11 : Bool) (x10 : Bool) (_ : (x10 && x11) = x1) (x01 : Bool) (x00 : Bool) (_ : (x00 && x01) = x0) : x00 = true := by bv_decide
theorem t3 (_ : x = true) (x1 : Bool) (x0 : Bool) (_ : (x0 && x1) = x) (x11 : Bool) (x10 : Bool) (_ : (x10 && x11) = x1) (x111 : Bool) (x110 : Bool) (_ : (x110 && x111) = x11) (x101 : Bool) (x100 : Bool) (_ : (x100 && x101) = x10) (x01 : Bool) (x00 : Bool) (_ : (x00 && x01) = x0) (x011 : Bool) (x010 : Bool) (_ : (x010 && x011) = x01) (x001 : Bool) (x000 : Bool) (_ : (x000 && x001) = x00) : x000 = true := by bv_decide
theorem t4 (_ : x = true) (x1 : Bool) (x0 : Bool) (_ : (x0 && x1) = x) (x11 : Bool) (x10 : Bool) (_ : (x10 && x11) = x1) (x111 : Bool) (x110 : Bool) (_ : (x110 && x111) = x11) (x1111 : Bool) (x1110 : Bool) (_ : (x1110 && x1111) = x111) (x1101 : Bool) (x1100 : Bool) (_ : (x1100 && x1101) = x110) (x101 : Bool) (x100 : Bool) (_ : (x100 && x101) = x10) (x1011 : Bool) (x1010 : Bool) (_ : (x1010 && x1011) = x101) (x1001 : Bool) (x1000 : Bool) (_ : (x1000 && x1001) = x100) (x01 : Bool) (x00 : Bool) (_ : (x00 && x01) = x0) (x011 : Bool) (x010 : Bool) (_ : (x010 && x011) = x01) (x0111 : Bool) (x0110 : Bool) (_ : (x0110 && x0111) = x011) (x0101 : Bool) (x0100 : Bool) (_ : (x0100 && x0101) = x010) (x001 : Bool) (x000 : Bool) (_ : (x000 && x001) = x00) (x0011 : Bool) (x0010 : Bool) (_ : (x0010 && x0011) = x001) (x0001 : Bool) (x0000 : Bool) (_ : (x0000 && x0001) = x000) : x0000 = true := by bv_decide
theorem t5 (_ : x = true) (x1 : Bool) (x0 : Bool) (_ : (x0 && x1) = x) (x11 : Bool) (x10 : Bool) (_ : (x10 && x11) = x1) (x111 : Bool) (x110 : Bool) (_ : (x110 && x111) = x11) (x1111 : Bool) (x1110 : Bool) (_ : (x1110 && x1111) = x111) (x11111 : Bool) (x11110 : Bool) (_ : (x11110 && x11111) = x1111) (x11101 : Bool) (x11100 : Bool) (_ : (x11100 && x11101) = x1110) (x1101 : Bool) (x1100 : Bool) (_ : (x1100 && x1101) = x110) (x11011 : Bool) (x11010 : Bool) (_ : (x11010 && x11011) = x1101) (x11001 : Bool) (x11000 : Bool) (_ : (x11000 && x11001) = x1100) (x101 : Bool) (x100 : Bool) (_ : (x100 && x101) = x10) (x1011 : Bool) (x1010 : Bool) (_ : (x1010 && x1011) = x101) (x10111 : Bool) (x10110 : Bool) (_ : (x10110 && x10111) = x1011) (x10101 : Bool) (x10100 : Bool) (_ : (x10100 && x10101) = x1010) (x1001 : Bool) (x1000 : Bool) (_ : (x1000 && x1001) = x100) (x10011 : Bool) (x10010 : Bool) (_ : (x10010 && x10011) = x1001) (x10001 : Bool) (x10000 : Bool) (_ : (x10000 && x10001) = x1000) (x01 : Bool) (x00 : Bool) (_ : (x00 && x01) = x0) (x011 : Bool) (x010 : Bool) (_ : (x010 && x011) = x01) (x0111 : Bool) (x0110 : Bool) (_ : (x0110 && x0111) = x011) (x01111 : Bool) (x01110 : Bool) (_ : (x01110 && x01111) = x0111) (x01101 : Bool) (x01100 : Bool) (_ : (x01100 && x01101) = x0110) (x0101 : Bool) (x0100 : Bool) (_ : (x0100 && x0101) = x010) (x01011 : Bool) (x01010 : Bool) (_ : (x01010 && x01011) = x0101) (x01001 : Bool) (x01000 : Bool) (_ : (x01000 && x01001) = x0100) (x001 : Bool) (x000 : Bool) (_ : (x000 && x001) = x00) (x0011 : Bool) (x0010 : Bool) (_ : (x0010 && x0011) = x001) (x00111 : Bool) (x00110 : Bool) (_ : (x00110 && x00111) = x0011) (x00101 : Bool) (x00100 : Bool) (_ : (x00100 && x00101) = x0010) (x0001 : Bool) (x0000 : Bool) (_ : (x0000 && x0001) = x000) (x00011 : Bool) (x00010 : Bool) (_ : (x00010 && x00011) = x0001) (x00001 : Bool) (x00000 : Bool) (_ : (x00000 && x00001) = x0000) : x00000 = true := by bv_decide
theorem t6 (_ : x = true) (x1 : Bool) (x0 : Bool) (_ : (x0 && x1) = x) (x11 : Bool) (x10 : Bool) (_ : (x10 && x11) = x1) (x111 : Bool) (x110 : Bool) (_ : (x110 && x111) = x11) (x1111 : Bool) (x1110 : Bool) (_ : (x1110 && x1111) = x111) (x11111 : Bool) (x11110 : Bool) (_ : (x11110 && x11111) = x1111) (x111111 : Bool) (x111110 : Bool) (_ : (x111110 && x111111) = x11111) (x111101 : Bool) (x111100 : Bool) (_ : (x111100 && x111101) = x11110) (x11101 : Bool) (x11100 : Bool) (_ : (x11100 && x11101) = x1110) (x111011 : Bool) (x111010 : Bool) (_ : (x111010 && x111011) = x11101) (x111001 : Bool) (x111000 : Bool) (_ : (x111000 && x111001) = x11100) (x1101 : Bool) (x1100 : Bool) (_ : (x1100 && x1101) = x110) (x11011 : Bool) (x11010 : Bool) (_ : (x11010 && x11011) = x1101) (x110111 : Bool) (x110110 : Bool) (_ : (x110110 && x110111) = x11011) (x110101 : Bool) (x110100 : Bool) (_ : (x110100 && x110101) = x11010) (x11001 : Bool) (x11000 : Bool) (_ : (x11000 && x11001) = x1100) (x110011 : Bool) (x110010 : Bool) (_ : (x110010 && x110011) = x11001) (x110001 : Bool) (x110000 : Bool) (_ : (x110000 && x110001) = x11000) (x101 : Bool) (x100 : Bool) (_ : (x100 && x101) = x10) (x1011 : Bool) (x1010 : Bool) (_ : (x1010 && x1011) = x101) (x10111 : Bool) (x10110 : Bool) (_ : (x10110 && x10111) = x1011) (x101111 : Bool) (x101110 : Bool) (_ : (x101110 && x101111) = x10111) (x101101 : Bool) (x101100 : Bool) (_ : (x101100 && x101101) = x10110) (x10101 : Bool) (x10100 : Bool) (_ : (x10100 && x10101) = x1010) (x101011 : Bool) (x101010 : Bool) (_ : (x101010 && x101011) = x10101) (x101001 : Bool) (x101000 : Bool) (_ : (x101000 && x101001) = x10100) (x1001 : Bool) (x1000 : Bool) (_ : (x1000 && x1001) = x100) (x10011 : Bool) (x10010 : Bool) (_ : (x10010 && x10011) = x1001) (x100111 : Bool) (x100110 : Bool) (_ : (x100110 && x100111) = x10011) (x100101 : Bool) (x100100 : Bool) (_ : (x100100 && x100101) = x10010) (x10001 : Bool) (x10000 : Bool) (_ : (x10000 && x10001) = x1000) (x100011 : Bool) (x100010 : Bool) (_ : (x100010 && x100011) = x10001) (x100001 : Bool) (x100000 : Bool) (_ : (x100000 && x100001) = x10000) (x01 : Bool) (x00 : Bool) (_ : (x00 && x01) = x0) (x011 : Bool) (x010 : Bool) (_ : (x010 && x011) = x01) (x0111 : Bool) (x0110 : Bool) (_ : (x0110 && x0111) = x011) (x01111 : Bool) (x01110 : Bool) (_ : (x01110 && x01111) = x0111) (x011111 : Bool) (x011110 : Bool) (_ : (x011110 && x011111) = x01111) (x011101 : Bool) (x011100 : Bool) (_ : (x011100 && x011101) = x01110) (x01101 : Bool) (x01100 : Bool) (_ : (x01100 && x01101) = x0110) (x011011 : Bool) (x011010 : Bool) (_ : (x011010 && x011011) = x01101) (x011001 : Bool) (x011000 : Bool) (_ : (x011000 && x011001) = x01100) (x0101 : Bool) (x0100 : Bool) (_ : (x0100 && x0101) = x010) (x01011 : Bool) (x01010 : Bool) (_ : (x01010 && x01011) = x0101) (x010111 : Bool) (x010110 : Bool) (_ : (x010110 && x010111) = x01011) (x010101 : Bool) (x010100 : Bool) (_ : (x010100 && x010101) = x01010) (x01001 : Bool) (x01000 : Bool) (_ : (x01000 && x01001) = x0100) (x010011 : Bool) (x010010 : Bool) (_ : (x010010 && x010011) = x01001) (x010001 : Bool) (x010000 : Bool) (_ : (x010000 && x010001) = x01000) (x001 : Bool) (x000 : Bool) (_ : (x000 && x001) = x00) (x0011 : Bool) (x0010 : Bool) (_ : (x0010 && x0011) = x001) (x00111 : Bool) (x00110 : Bool) (_ : (x00110 && x00111) = x0011) (x001111 : Bool) (x001110 : Bool) (_ : (x001110 && x001111) = x00111) (x001101 : Bool) (x001100 : Bool) (_ : (x001100 && x001101) = x00110) (x00101 : Bool) (x00100 : Bool) (_ : (x00100 && x00101) = x0010) (x001011 : Bool) (x001010 : Bool) (_ : (x001010 && x001011) = x00101) (x001001 : Bool) (x001000 : Bool) (_ : (x001000 && x001001) = x00100) (x0001 : Bool) (x0000 : Bool) (_ : (x0000 && x0001) = x000) (x00011 : Bool) (x00010 : Bool) (_ : (x00010 && x00011) = x0001) (x000111 : Bool) (x000110 : Bool) (_ : (x000110 && x000111) = x00011) (x000101 : Bool) (x000100 : Bool) (_ : (x000100 && x000101) = x00010) (x00001 : Bool) (x00000 : Bool) (_ : (x00000 && x00001) = x0000) (x000011 : Bool) (x000010 : Bool) (_ : (x000010 && x000011) = x00001) (x000001 : Bool) (x000000 : Bool) (_ : (x000000 && x000001) = x00000) : x000000 = true := by bv_decide

/-!
# Binary `and` of 2^7 variables
~2.3s
-/
theorem t7 (_ : x = true) (x1 : Bool) (x0 : Bool) (_ : (x0 && x1) = x) (x11 : Bool) (x10 : Bool) (_ : (x10 && x11) = x1) (x111 : Bool) (x110 : Bool) (_ : (x110 && x111) = x11) (x1111 : Bool) (x1110 : Bool) (_ : (x1110 && x1111) = x111) (x11111 : Bool) (x11110 : Bool) (_ : (x11110 && x11111) = x1111) (x111111 : Bool) (x111110 : Bool) (_ : (x111110 && x111111) = x11111) (x1111111 : Bool) (x1111110 : Bool) (_ : (x1111110 && x1111111) = x111111) (x1111101 : Bool) (x1111100 : Bool) (_ : (x1111100 && x1111101) = x111110) (x111101 : Bool) (x111100 : Bool) (_ : (x111100 && x111101) = x11110) (x1111011 : Bool) (x1111010 : Bool) (_ : (x1111010 && x1111011) = x111101) (x1111001 : Bool) (x1111000 : Bool) (_ : (x1111000 && x1111001) = x111100) (x11101 : Bool) (x11100 : Bool) (_ : (x11100 && x11101) = x1110) (x111011 : Bool) (x111010 : Bool) (_ : (x111010 && x111011) = x11101) (x1110111 : Bool) (x1110110 : Bool) (_ : (x1110110 && x1110111) = x111011) (x1110101 : Bool) (x1110100 : Bool) (_ : (x1110100 && x1110101) = x111010) (x111001 : Bool) (x111000 : Bool) (_ : (x111000 && x111001) = x11100) (x1110011 : Bool) (x1110010 : Bool) (_ : (x1110010 && x1110011) = x111001) (x1110001 : Bool) (x1110000 : Bool) (_ : (x1110000 && x1110001) = x111000) (x1101 : Bool) (x1100 : Bool) (_ : (x1100 && x1101) = x110) (x11011 : Bool) (x11010 : Bool) (_ : (x11010 && x11011) = x1101) (x110111 : Bool) (x110110 : Bool) (_ : (x110110 && x110111) = x11011) (x1101111 : Bool) (x1101110 : Bool) (_ : (x1101110 && x1101111) = x110111) (x1101101 : Bool) (x1101100 : Bool) (_ : (x1101100 && x1101101) = x110110) (x110101 : Bool) (x110100 : Bool) (_ : (x110100 && x110101) = x11010) (x1101011 : Bool) (x1101010 : Bool) (_ : (x1101010 && x1101011) = x110101) (x1101001 : Bool) (x1101000 : Bool) (_ : (x1101000 && x1101001) = x110100) (x11001 : Bool) (x11000 : Bool) (_ : (x11000 && x11001) = x1100) (x110011 : Bool) (x110010 : Bool) (_ : (x110010 && x110011) = x11001) (x1100111 : Bool) (x1100110 : Bool) (_ : (x1100110 && x1100111) = x110011) (x1100101 : Bool) (x1100100 : Bool) (_ : (x1100100 && x1100101) = x110010) (x110001 : Bool) (x110000 : Bool) (_ : (x110000 && x110001) = x11000) (x1100011 : Bool) (x1100010 : Bool) (_ : (x1100010 && x1100011) = x110001) (x1100001 : Bool) (x1100000 : Bool) (_ : (x1100000 && x1100001) = x110000) (x101 : Bool) (x100 : Bool) (_ : (x100 && x101) = x10) (x1011 : Bool) (x1010 : Bool) (_ : (x1010 && x1011) = x101) (x10111 : Bool) (x10110 : Bool) (_ : (x10110 && x10111) = x1011) (x101111 : Bool) (x101110 : Bool) (_ : (x101110 && x101111) = x10111) (x1011111 : Bool) (x1011110 : Bool) (_ : (x1011110 && x1011111) = x101111) (x1011101 : Bool) (x1011100 : Bool) (_ : (x1011100 && x1011101) = x101110) (x101101 : Bool) (x101100 : Bool) (_ : (x101100 && x101101) = x10110) (x1011011 : Bool) (x1011010 : Bool) (_ : (x1011010 && x1011011) = x101101) (x1011001 : Bool) (x1011000 : Bool) (_ : (x1011000 && x1011001) = x101100) (x10101 : Bool) (x10100 : Bool) (_ : (x10100 && x10101) = x1010) (x101011 : Bool) (x101010 : Bool) (_ : (x101010 && x101011) = x10101) (x1010111 : Bool) (x1010110 : Bool) (_ : (x1010110 && x1010111) = x101011) (x1010101 : Bool) (x1010100 : Bool) (_ : (x1010100 && x1010101) = x101010) (x101001 : Bool) (x101000 : Bool) (_ : (x101000 && x101001) = x10100) (x1010011 : Bool) (x1010010 : Bool) (_ : (x1010010 && x1010011) = x101001) (x1010001 : Bool) (x1010000 : Bool) (_ : (x1010000 && x1010001) = x101000) (x1001 : Bool) (x1000 : Bool) (_ : (x1000 && x1001) = x100) (x10011 : Bool) (x10010 : Bool) (_ : (x10010 && x10011) = x1001) (x100111 : Bool) (x100110 : Bool) (_ : (x100110 && x100111) = x10011) (x1001111 : Bool) (x1001110 : Bool) (_ : (x1001110 && x1001111) = x100111) (x1001101 : Bool) (x1001100 : Bool) (_ : (x1001100 && x1001101) = x100110) (x100101 : Bool) (x100100 : Bool) (_ : (x100100 && x100101) = x10010) (x1001011 : Bool) (x1001010 : Bool) (_ : (x1001010 && x1001011) = x100101) (x1001001 : Bool) (x1001000 : Bool) (_ : (x1001000 && x1001001) = x100100) (x10001 : Bool) (x10000 : Bool) (_ : (x10000 && x10001) = x1000) (x100011 : Bool) (x100010 : Bool) (_ : (x100010 && x100011) = x10001) (x1000111 : Bool) (x1000110 : Bool) (_ : (x1000110 && x1000111) = x100011) (x1000101 : Bool) (x1000100 : Bool) (_ : (x1000100 && x1000101) = x100010) (x100001 : Bool) (x100000 : Bool) (_ : (x100000 && x100001) = x10000) (x1000011 : Bool) (x1000010 : Bool) (_ : (x1000010 && x1000011) = x100001) (x1000001 : Bool) (x1000000 : Bool) (_ : (x1000000 && x1000001) = x100000) (x01 : Bool) (x00 : Bool) (_ : (x00 && x01) = x0) (x011 : Bool) (x010 : Bool) (_ : (x010 && x011) = x01) (x0111 : Bool) (x0110 : Bool) (_ : (x0110 && x0111) = x011) (x01111 : Bool) (x01110 : Bool) (_ : (x01110 && x01111) = x0111) (x011111 : Bool) (x011110 : Bool) (_ : (x011110 && x011111) = x01111) (x0111111 : Bool) (x0111110 : Bool) (_ : (x0111110 && x0111111) = x011111) (x0111101 : Bool) (x0111100 : Bool) (_ : (x0111100 && x0111101) = x011110) (x011101 : Bool) (x011100 : Bool) (_ : (x011100 && x011101) = x01110) (x0111011 : Bool) (x0111010 : Bool) (_ : (x0111010 && x0111011) = x011101) (x0111001 : Bool) (x0111000 : Bool) (_ : (x0111000 && x0111001) = x011100) (x01101 : Bool) (x01100 : Bool) (_ : (x01100 && x01101) = x0110) (x011011 : Bool) (x011010 : Bool) (_ : (x011010 && x011011) = x01101) (x0110111 : Bool) (x0110110 : Bool) (_ : (x0110110 && x0110111) = x011011) (x0110101 : Bool) (x0110100 : Bool) (_ : (x0110100 && x0110101) = x011010) (x011001 : Bool) (x011000 : Bool) (_ : (x011000 && x011001) = x01100) (x0110011 : Bool) (x0110010 : Bool) (_ : (x0110010 && x0110011) = x011001) (x0110001 : Bool) (x0110000 : Bool) (_ : (x0110000 && x0110001) = x011000) (x0101 : Bool) (x0100 : Bool) (_ : (x0100 && x0101) = x010) (x01011 : Bool) (x01010 : Bool) (_ : (x01010 && x01011) = x0101) (x010111 : Bool) (x010110 : Bool) (_ : (x010110 && x010111) = x01011) (x0101111 : Bool) (x0101110 : Bool) (_ : (x0101110 && x0101111) = x010111) (x0101101 : Bool) (x0101100 : Bool) (_ : (x0101100 && x0101101) = x010110) (x010101 : Bool) (x010100 : Bool) (_ : (x010100 && x010101) = x01010) (x0101011 : Bool) (x0101010 : Bool) (_ : (x0101010 && x0101011) = x010101) (x0101001 : Bool) (x0101000 : Bool) (_ : (x0101000 && x0101001) = x010100) (x01001 : Bool) (x01000 : Bool) (_ : (x01000 && x01001) = x0100) (x010011 : Bool) (x010010 : Bool) (_ : (x010010 && x010011) = x01001) (x0100111 : Bool) (x0100110 : Bool) (_ : (x0100110 && x0100111) = x010011) (x0100101 : Bool) (x0100100 : Bool) (_ : (x0100100 && x0100101) = x010010) (x010001 : Bool) (x010000 : Bool) (_ : (x010000 && x010001) = x01000) (x0100011 : Bool) (x0100010 : Bool) (_ : (x0100010 && x0100011) = x010001) (x0100001 : Bool) (x0100000 : Bool) (_ : (x0100000 && x0100001) = x010000) (x001 : Bool) (x000 : Bool) (_ : (x000 && x001) = x00) (x0011 : Bool) (x0010 : Bool) (_ : (x0010 && x0011) = x001) (x00111 : Bool) (x00110 : Bool) (_ : (x00110 && x00111) = x0011) (x001111 : Bool) (x001110 : Bool) (_ : (x001110 && x001111) = x00111) (x0011111 : Bool) (x0011110 : Bool) (_ : (x0011110 && x0011111) = x001111) (x0011101 : Bool) (x0011100 : Bool) (_ : (x0011100 && x0011101) = x001110) (x001101 : Bool) (x001100 : Bool) (_ : (x001100 && x001101) = x00110) (x0011011 : Bool) (x0011010 : Bool) (_ : (x0011010 && x0011011) = x001101) (x0011001 : Bool) (x0011000 : Bool) (_ : (x0011000 && x0011001) = x001100) (x00101 : Bool) (x00100 : Bool) (_ : (x00100 && x00101) = x0010) (x001011 : Bool) (x001010 : Bool) (_ : (x001010 && x001011) = x00101) (x0010111 : Bool) (x0010110 : Bool) (_ : (x0010110 && x0010111) = x001011) (x0010101 : Bool) (x0010100 : Bool) (_ : (x0010100 && x0010101) = x001010) (x001001 : Bool) (x001000 : Bool) (_ : (x001000 && x001001) = x00100) (x0010011 : Bool) (x0010010 : Bool) (_ : (x0010010 && x0010011) = x001001) (x0010001 : Bool) (x0010000 : Bool) (_ : (x0010000 && x0010001) = x001000) (x0001 : Bool) (x0000 : Bool) (_ : (x0000 && x0001) = x000) (x00011 : Bool) (x00010 : Bool) (_ : (x00010 && x00011) = x0001) (x000111 : Bool) (x000110 : Bool) (_ : (x000110 && x000111) = x00011) (x0001111 : Bool) (x0001110 : Bool) (_ : (x0001110 && x0001111) = x000111) (x0001101 : Bool) (x0001100 : Bool) (_ : (x0001100 && x0001101) = x000110) (x000101 : Bool) (x000100 : Bool) (_ : (x000100 && x000101) = x00010) (x0001011 : Bool) (x0001010 : Bool) (_ : (x0001010 && x0001011) = x000101) (x0001001 : Bool) (x0001000 : Bool) (_ : (x0001000 && x0001001) = x000100) (x00001 : Bool) (x00000 : Bool) (_ : (x00000 && x00001) = x0000) (x000011 : Bool) (x000010 : Bool) (_ : (x000010 && x000011) = x00001) (x0000111 : Bool) (x0000110 : Bool) (_ : (x0000110 && x0000111) = x000011) (x0000101 : Bool) (x0000100 : Bool) (_ : (x0000100 && x0000101) = x000010) (x000001 : Bool) (x000000 : Bool) (_ : (x000000 && x000001) = x00000) (x0000011 : Bool) (x0000010 : Bool) (_ : (x0000010 && x0000011) = x000001) (x0000001 : Bool) (x0000000 : Bool) (_ : (x0000000 && x0000001) = x000000) : x0000000 = true := by bv_decide
