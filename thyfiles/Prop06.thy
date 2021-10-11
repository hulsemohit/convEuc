theory Prop06
	imports Geometry Prop06a angledistinct collinearorder equalanglessymmetric trichotomy1
begin

theorem(in euclidean_geometry) Prop06:
	assumes 
		"triangle A B C"
		"ang_eq A B C A C B"
	shows "seg_eq A B A C"
proof -
	have "\<not> (seg_lt A C A B)" using Prop06a[OF `triangle A B C` `ang_eq A B C A C B`] .
	have "\<not> col A B C" using triangle_f[OF `triangle A B C`] .
	have "\<not> (col A C B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A C B))"
hence "col A C B" by blast
		have "col A B C" using collinearorder[OF `col A C B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col A C B" by blast
	have "triangle A C B" using triangle_b[OF `\<not> col A C B`] .
	have "ang_eq A C B A B C" using equalanglessymmetric[OF `ang_eq A B C A C B`] .
	have "\<not> (seg_lt A B A C)" using Prop06a[OF `triangle A C B` `ang_eq A C B A B C`] .
	have "A \<noteq> B" using angledistinct[OF `ang_eq A B C A C B`] by blast
	have "A \<noteq> C" using angledistinct[OF `ang_eq A B C A C B`] by blast
	have "seg_eq A B A C" using trichotomy1[OF `\<not> (seg_lt A B A C)` `\<not> (seg_lt A C A B)` `A \<noteq> B` `A \<noteq> C`] .
	thus ?thesis by blast
qed

end