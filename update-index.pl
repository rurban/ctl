#!/usr/bin/perl

open my $in, '<', 'README.md' or die "$! README.md";
my $outfn = 'docs/index.md';
open my $out, '>', "$outfn.tmp" or die "$! $outfn.tmp";
while (<$in>) {
  s {docs/images/} {images/};
  s {\(docs/} {\(};
  print $out $_;
}
close $in;
close $out;
if (system "diff $outfn $outfn.tmp") {
  system "mv $outfn.tmp $outfn";
} else {
  system "rm $outfn.tmp";
}

