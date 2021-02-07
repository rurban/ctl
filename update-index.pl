#!/usr/bin/perl

open my $in, '<', 'README.md' or die "$! README.md";
my $outfn = 'docs/index.md';
open my $out, '>', "$outfn.tmp" or die "$! $outfn.tmp";
my $prev = '';
while (<$in>) {
  if ($prev eq "\n" and /^\|  +\|vec/) {
    print $out "```\n";
  }
  s {docs/images/} {images/};
  s {\(docs/} {\(};
  if ($prev =~ /^\|  +\|vec/ and /^## /) {
    print $out "```\n";
  }
  print $out $_;
  $prev = $_;
}
close $in;
close $out;
if (system "diff $outfn $outfn.tmp") {
  system "mv $outfn.tmp $outfn";
} else {
  system "rm $outfn.tmp";
}

