theory parallelcollinear
	imports Axioms Definitions Theorems
begin

theorem parallelcollinear:
	assumes: `axioms`
		"tarski_parallel A B c d"
		"col c d C"
		"C \<noteq> d"
	shows: "tarski_parallel A B C d"
proof -
	have "c \<noteq> d" using tarski_parallel_f[OF `axioms` `tarski_parallel A B c d`] by blast
	have "c = d \<or> c = C \<or> d = C \<or> bet d c C \<or> bet c d C \<or> bet c C d" using collinear_f[OF `axioms` `col c d C`] .
	consider "c = d"|"c = C"|"d = C"|"bet d c C"|"bet c d C"|"bet c C d" using `c = d \<or> c = C \<or> d = C \<or> bet d c C \<or> bet c d C \<or> bet c C d`  by blast
	hence tarski_parallel A B C d
	proof (cases)
		case 1
		have "tarski_parallel A B C d"
		proof (rule ccontr)
			assume "\<not> (tarski_parallel A B C d)"
			have "c \<noteq> d" using `c \<noteq> d` .
			show "False" using `c \<noteq> d` `c = d` by blast
		qed
		hence "tarski_parallel A B C d" by blast
	next
		case 2
		have "tarski_parallel A B C d" using `tarski_parallel A B c d` `c = C` by blast
	next
		case 3
		have "tarski_parallel A B C d"
		proof (rule ccontr)
			assume "\<not> (tarski_parallel A B C d)"
			have "C = d" using equalitysymmetric[OF `axioms` `d = C`] .
			show "False" using `C = d` `C \<noteq> d` by blast
		qed
		hence "tarski_parallel A B C d" by blast
	next
		case 4
		have "bet C c d" using betweennesssymmetryE[OF `axioms` `bet d c C`] .
		have "tarski_parallel A B C d" using parallelcollinear1[OF `axioms` `tarski_parallel A B c d` `bet C c d`] .
	next
		case 5
		have "bet C d c" using betweennesssymmetryE[OF `axioms` `bet c d C`] .
		have "tarski_parallel A B d c" using tarskiparallelflip[OF `axioms` `tarski_parallel A B c d`] by blast
		have "tarski_parallel A B C c" using parallelcollinear1[OF `axioms` `tarski_parallel A B d c` `bet C d c`] .
		have "tarski_parallel A B c C" using tarskiparallelflip[OF `axioms` `tarski_parallel A B C c`] by blast
		have "tarski_parallel A B d C" using parallelcollinear2[OF `axioms` `tarski_parallel A B c C` `bet c d C`] .
		have "tarski_parallel A B C d" using tarskiparallelflip[OF `axioms` `tarski_parallel A B d C`] by blast
	next
		case 5
		have "tarski_parallel A B C d" using parallelcollinear2[OF `axioms` `tarski_parallel A B c d` `bet c C d`] .
	next
	thus ?thesis by blast
qed

end