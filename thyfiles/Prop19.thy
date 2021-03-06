theory Prop19
	imports ABCequalsCBA Geometry NCorder Prop05 Prop18 angledistinct angleorderrespectscongruence angleorderrespectscongruence2 angletrichotomy congruencesymmetric equalanglesreflexive equalanglessymmetric equalanglestransitive trichotomy1
begin

theorem(in euclidean_geometry) Prop19:
	assumes 
		"triangle A B C"
		"ang_lt B C A A B C"
	shows "seg_lt A B A C"
proof -
	have "\<not> col A B C" using triangle_f[OF `triangle A B C`] .
	have "\<not> col B C A" using NCorder[OF `\<not> col A B C`] by blast
	have "\<not> col A C B" using NCorder[OF `\<not> col A B C`] by blast
	have "\<not> (seg_eq A C A B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (seg_eq A C A B))"
hence "seg_eq A C A B" by blast
		have "seg_eq A B A C" using congruencesymmetric[OF `seg_eq A C A B`] .
		have "tri_isos A B C" using isosceles_b[OF `triangle A B C` `seg_eq A B A C`] .
		have "ang_eq A B C A C B" using Prop05[OF `tri_isos A B C`] .
		have "ang_eq A C B A B C" using equalanglessymmetric[OF `ang_eq A B C A C B`] .
		have "\<not> col B C A" using `\<not> col B C A` .
		have "ang_eq B C A A C B" using ABCequalsCBA[OF `\<not> col B C A`] .
		have "ang_eq B C A A B C" using equalanglestransitive[OF `ang_eq B C A A C B` `ang_eq A C B A B C`] .
		have "ang_lt B C A B C A" using angleorderrespectscongruence[OF `ang_lt B C A A B C` `ang_eq B C A A B C`] .
		have "\<not> (ang_lt B C A B C A)" using angletrichotomy[OF `ang_lt B C A B C A`] .
		show "False" using `\<not> (ang_lt B C A B C A)` `ang_lt B C A B C A` by blast
	qed
	hence "\<not> (seg_eq A C A B)" by blast
	have "\<not> (seg_lt A C A B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (seg_lt A C A B))"
hence "seg_lt A C A B" by blast
		have "triangle A C B" using triangle_b[OF `\<not> col A C B`] .
		have "ang_lt C B A A C B" using Prop18[OF `triangle A C B` `seg_lt A C A B`] .
		have "ang_eq A B C C B A" using ABCequalsCBA[OF `\<not> col A B C`] .
		have "ang_lt A B C A C B" using angleorderrespectscongruence2[OF `ang_lt C B A A C B` `ang_eq A B C C B A`] .
		have "ang_eq B C A A C B" using ABCequalsCBA[OF `\<not> col B C A`] .
		have "ang_lt A B C B C A" using angleorderrespectscongruence[OF `ang_lt A B C A C B` `ang_eq B C A A C B`] .
		have "ang_lt B C A A B C" using `ang_lt B C A A B C` .
		have "\<not> (ang_lt A B C B C A)" using angletrichotomy[OF `ang_lt B C A A B C`] .
		show "False" using `\<not> (ang_lt A B C B C A)` `ang_lt A B C B C A` by blast
	qed
	hence "\<not> (seg_lt A C A B)" by blast
	have "ang_eq A B C A B C" using equalanglesreflexive[OF `\<not> col A B C`] .
	have "A \<noteq> B" using angledistinct[OF `ang_eq A B C A B C`] by blast
	have "A \<noteq> C" using angledistinct[OF `ang_eq A B C A B C`] by blast
	have "\<not> (\<not> (seg_lt A B A C))"
	proof (rule ccontr)
		assume "\<not> (\<not> (\<not> (seg_lt A B A C)))"
hence "\<not> (seg_lt A B A C)" by blast
		have "seg_eq A B A C" using trichotomy1[OF `\<not> (seg_lt A B A C)` `\<not> (seg_lt A C A B)` `A \<noteq> B` `A \<noteq> C`] .
		have "seg_eq A C A B" using congruencesymmetric[OF `seg_eq A B A C`] .
		show "False" using `seg_eq A C A B` `\<not> (seg_eq A C A B)` by blast
	qed
	hence "seg_lt A B A C" by blast
	thus ?thesis by blast
qed

end