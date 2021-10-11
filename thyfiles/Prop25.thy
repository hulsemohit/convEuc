theory Prop25
	imports Geometry Prop04 Prop24 angletrichotomy2 collinearorder congruencesymmetric equalanglessymmetric lessthancongruence2 trichotomy2
begin

theorem(in euclidean_geometry) Prop25:
	assumes 
		"triangle A B C"
		"triangle D E F"
		"seg_eq A B D E"
		"seg_eq A C D F"
		"seg_lt E F B C"
	shows "ang_lt E D F B A C"
proof -
	have "seg_eq D E A B" using congruencesymmetric[OF `seg_eq A B D E`] .
	have "seg_eq D F A C" using congruencesymmetric[OF `seg_eq A C D F`] .
	have "\<not> (ang_lt B A C E D F)"
	proof (rule ccontr)
		assume "\<not> (\<not> (ang_lt B A C E D F))"
hence "ang_lt B A C E D F" by blast
		have "seg_lt B C E F" using Prop24[OF `triangle D E F` `triangle A B C` `seg_eq D E A B` `seg_eq D F A C` `ang_lt B A C E D F`] .
		have "\<not> (seg_lt E F B C)" using trichotomy2[OF `seg_lt B C E F`] .
		show "False" using `\<not> (seg_lt E F B C)` `seg_lt E F B C` by blast
	qed
	hence "\<not> (ang_lt B A C E D F)" by blast
	have "\<not> col A B C" using triangle_f[OF `triangle A B C`] .
	have "\<not> (col B A C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B A C))"
hence "col B A C" by blast
		have "col A B C" using collinearorder[OF `col B A C`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B A C" by blast
	have "\<not> col D E F" using triangle_f[OF `triangle D E F`] .
	have "\<not> (col E D F)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col E D F))"
hence "col E D F" by blast
		have "col D E F" using collinearorder[OF `col E D F`] by blast
		show "False" using `col D E F` `\<not> col D E F` by blast
	qed
	hence "\<not> col E D F" by blast
	have "\<not> (ang_eq E D F B A C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (ang_eq E D F B A C))"
hence "ang_eq E D F B A C" by blast
		have "ang_eq B A C E D F" using equalanglessymmetric[OF `ang_eq E D F B A C`] .
		have "seg_eq B C E F" using Prop04[OF `seg_eq A B D E` `seg_eq A C D F` `ang_eq B A C E D F`] by blast
		have "seg_eq E F B C" using congruencesymmetric[OF `seg_eq B C E F`] .
		have "seg_lt B C B C" using lessthancongruence2[OF `seg_lt E F B C` `seg_eq E F B C`] .
		have "\<not> (seg_lt B C B C)" using trichotomy2[OF `seg_lt B C B C`] .
		show "False" using `\<not> (seg_lt B C B C)` `seg_lt B C B C` by blast
	qed
	hence "\<not> (ang_eq E D F B A C)" by blast
	have "ang_lt E D F B A C" using angletrichotomy2[OF `\<not> col E D F` `\<not> col B A C` `\<not> (ang_eq E D F B A C)` `\<not> (ang_lt B A C E D F)`] .
	thus ?thesis by blast
qed

end