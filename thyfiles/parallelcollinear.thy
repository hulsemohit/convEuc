theory parallelcollinear
	imports Geometry equalitysymmetric parallelcollinear1 parallelcollinear2 tarskiparallelflip
begin

theorem(in euclidean_geometry) parallelcollinear:
	assumes 
		"tarski_parallel A B c d"
		"col c d C"
		"C \<noteq> d"
	shows "tarski_parallel A B C d"
proof -
	have "c \<noteq> d" using tarski_parallel_f[OF `tarski_parallel A B c d`] by blast
	have "c = d \<or> c = C \<or> d = C \<or> bet d c C \<or> bet c d C \<or> bet c C d" using collinear_f[OF `col c d C`] .
	consider "c = d"|"c = C"|"d = C"|"bet d c C"|"bet c d C"|"bet c C d" using `c = d \<or> c = C \<or> d = C \<or> bet d c C \<or> bet c d C \<or> bet c C d`  by blast
	hence "tarski_parallel A B C d"
	proof (cases)
		assume "c = d"
		have "\<not> (\<not> (tarski_parallel A B C d))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (tarski_parallel A B C d)))"
hence "\<not> (tarski_parallel A B C d)" by blast
			have "c \<noteq> d" using `c \<noteq> d` .
			show "False" using `c \<noteq> d` `c = d` by blast
		qed
		hence "tarski_parallel A B C d" by blast
		thus ?thesis by blast
	next
		assume "c = C"
		have "tarski_parallel A B C d" using `tarski_parallel A B c d` `c = C` by blast
		thus ?thesis by blast
	next
		assume "d = C"
		have "\<not> (\<not> (tarski_parallel A B C d))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (tarski_parallel A B C d)))"
hence "\<not> (tarski_parallel A B C d)" by blast
			have "C = d" using equalitysymmetric[OF `d = C`] .
			show "False" using `C = d` `C \<noteq> d` by blast
		qed
		hence "tarski_parallel A B C d" by blast
		thus ?thesis by blast
	next
		assume "bet d c C"
		have "bet C c d" using betweennesssymmetryE[OF `bet d c C`] .
		have "tarski_parallel A B C d" using parallelcollinear1[OF `tarski_parallel A B c d` `bet C c d`] .
		thus ?thesis by blast
	next
		assume "bet c d C"
		have "bet C d c" using betweennesssymmetryE[OF `bet c d C`] .
		have "tarski_parallel A B d c" using tarskiparallelflip[OF `tarski_parallel A B c d`] by blast
		have "tarski_parallel A B C c" using parallelcollinear1[OF `tarski_parallel A B d c` `bet C d c`] .
		have "tarski_parallel A B c C" using tarskiparallelflip[OF `tarski_parallel A B C c`] by blast
		have "tarski_parallel A B d C" using parallelcollinear2[OF `tarski_parallel A B c C` `bet c d C`] .
		have "tarski_parallel A B C d" using tarskiparallelflip[OF `tarski_parallel A B d C`] by blast
		thus ?thesis by blast
	next
		assume "bet c C d"
		have "tarski_parallel A B C d" using parallelcollinear2[OF `tarski_parallel A B c d` `bet c C d`] .
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end