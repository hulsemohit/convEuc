theory Prop05b
	imports Geometry Prop05 collinearorder equalanglesNC inequalitysymmetric ray4 supplements
begin

theorem(in euclidean_geometry) Prop05b:
	assumes 
		"tri_isos A B C"
		"bet A B F"
		"bet A C G"
	shows "ang_eq C B F B C G"
proof -
	have "ang_eq A B C A C B" using Prop05[OF `tri_isos A B C`] .
	have "C = C" using equalityreflexiveE.
	have "\<not> col A C B" using equalanglesNC[OF `ang_eq A B C A C B`] .
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> C)"
		hence "B = C" by blast
		have "col A B C" using collinear_b `B = C` by blast
		have "col A C B" using collinearorder[OF `col A B C`] by blast
		show "False" using `col A C B` `\<not> col A C B` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	have "ray_on B C C" using ray4 `C = C` `B \<noteq> C` by blast
	have "bet A B F \<and> ray_on B C C" using `bet A B F` `ray_on B C C` by blast
	have "supplement A B C C F" using supplement_b[OF `ray_on B C C` `bet A B F`] .
	have "B = B" using equalityreflexiveE.
	have "ray_on C B B" using ray4 `B = B` `C \<noteq> B` by blast
	have "ray_on C B B \<and> bet A C G" using `ray_on C B B` `bet A C G` by blast
	have "supplement A C B B G" using supplement_b[OF `ray_on C B B` `bet A C G`] .
	have "ang_eq C B F B C G" using supplements[OF `ang_eq A B C A C B` `supplement A B C C F` `supplement A C B B G`] .
	thus ?thesis by blast
qed

end