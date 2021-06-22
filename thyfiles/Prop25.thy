theory Prop25
	imports Axioms Definitions Theorems
begin

theorem Prop25:
	assumes: `axioms`
		"triangle A B C"
		"triangle D E F"
		"seg_eq A B D E"
		"seg_eq A C D F"
		"seg_lt E F B C"
	shows: "ang_lt E D F B A C"
proof -
	have "seg_eq D E A B" using congruencesymmetric[OF `axioms` `seg_eq A B D E`] .
	have "seg_eq D F A C" using congruencesymmetric[OF `axioms` `seg_eq A C D F`] .
	have "\<not> (ang_lt B A C E D F)"
	proof (rule ccontr)
		assume "ang_lt B A C E D F"
		have "seg_lt B C E F" using Prop24[OF `axioms` `triangle D E F` `triangle A B C` `seg_eq D E A B` `seg_eq D F A C` `ang_lt B A C E D F`] .
		have "\<not> (seg_lt E F B C)" using trichotomy2[OF `axioms` `seg_lt B C E F`] .
		show "False" using `\<not> (seg_lt E F B C)` `seg_lt E F B C` by blast
	qed
	hence "\<not> (ang_lt B A C E D F)" by blast
	have "\<not> col A B C" using triangle_f[OF `axioms` `triangle A B C`] .
	have "\<not> (col B A C)"
	proof (rule ccontr)
		assume "col B A C"
		have "col A B C" using collinearorder[OF `axioms` `col B A C`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B A C" by blast
	have "\<not> col D E F" using triangle_f[OF `axioms` `triangle D E F`] .
	have "\<not> (col E D F)"
	proof (rule ccontr)
		assume "col E D F"
		have "col D E F" using collinearorder[OF `axioms` `col E D F`] by blast
		show "False" using `col D E F` `\<not> col D E F` by blast
	qed
	hence "\<not> col E D F" by blast
	have "\<not> (ang_eq E D F B A C)"
	proof (rule ccontr)
		assume "ang_eq E D F B A C"
		have "ang_eq B A C E D F" using equalanglessymmetric[OF `axioms` `ang_eq E D F B A C`] .
		have "seg_eq B C E F" using Prop04[OF `axioms` `seg_eq A B D E` `seg_eq A C D F` `ang_eq B A C E D F`] by blast
		have "seg_eq E F B C" using congruencesymmetric[OF `axioms` `seg_eq B C E F`] .
		have "seg_lt B C B C" using lessthancongruence2[OF `axioms` `seg_lt E F B C` `seg_eq E F B C`] .
		have "\<not> (seg_lt B C B C)" using trichotomy2[OF `axioms` `seg_lt B C B C`] .
		show "False" using `\<not> (seg_lt B C B C)` `seg_lt B C B C` by blast
	qed
	hence "\<not> (ang_eq E D F B A C)" by blast
	have "ang_lt E D F B A C" using angletrichotomy2[OF `axioms` `\<not> col E D F` `\<not> col B A C` `\<not> (ang_eq E D F B A C)` `\<not> (ang_lt B A C E D F)`] .
	thus ?thesis by blast
qed

end