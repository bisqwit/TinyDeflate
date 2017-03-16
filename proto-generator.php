<?php

$inputs  = Array();
$outputs = Array();
$bodies  = Array();

/*********************************/

/* Input functor */
$inputs['Inf'] = Array(
  'templateparams' => Array('InputFunctor'),
  'enables'        => Array('DeflIsInputFunctor'),
  'params'         => Array('InputFunctor&& inputfun'),
  'abortable'      => ('DeflInputAbortable_Type(std::decay_t<std::result_of_t<InputFunctor()>>)'),
  'before'         => 'gunzip_ns::dummy btfun{};'
);
/* Input iterator */
$inputs['InI'] = Array(
  'templateparams' => Array('InputIterator'),
  'enables'        => Array('DeflIsInputIterator'),
  'params'         => Array('InputIterator&& input'),
  'abortable'      => ('DeflInputAbortable_Type(std::decay_t<decltype(*input)>)'),
  'before'         => 'auto inputfun = [&]() { auto r = *input; ++input; return r; };'."\n".
                      'gunzip_ns::dummy btfun{};'
);
/* Input iterator begin and end */
$inputs['InI2'] = Array(
  'templateparams' => Array('InputIterator'),
  'enables'        => Array('DeflIsInputIterator'),
  'params'         => Array('InputIterator&& begin', 'InputIterator&& end'),
  'abortable'      => ('1'),
  'before'         => 'auto inputfun = [&]() { if(begin==end) { return -1; } int r = *begin; ++begin; return r; };'."\n".
                      'gunzip_ns::dummy btfun{};'
);
/* Input iterator and number of bytes */
$inputs['InIl'] = Array(
  'templateparams' => Array('InputIterator',         'SizeType'),
  'enables'        => Array('DeflIsInputIterator',   'DeflIsSizeType'),
  'params'         => Array('InputIterator&& begin', 'SizeType&& length'),
  'abortable'      => ('1'),
  'before'         => 'typename std::iterator_traits<std::decay_t<InputIterator>>::difference_type remain(length);'."\n".
                      'auto inputfun = [&]() -> std::common_type_t<int, decltype(*begin)> '."\n".
                      '{ if(!remain) { return -1; } --remain; int r = *begin; ++begin; return r; };'."\n".
                      'gunzip_ns::dummy btfun{};'
);

/* Bidir iterator and number of bytes */
$inputs['InBl'] = Array(
  'templateparams' => Array('BidirIterator',        'SizeType'),
  'enables'        => Array('DeflIsBidirIterator',  'DeflIsSizeType'),
  'params'         => Array('BidirIterator&& begin', 'SizeType&& length'),
  'abortable'      => ('1'),
  'before'         => 'typename std::iterator_traits<std::decay_t<BidirIterator>>::difference_type remain(length), savestate{};'."\n".
                      'auto inputfun = [&]() -> std::common_type_t<int, decltype(*begin)> '."\n".
                      '{ if(!remain) { return -1; } --remain; int r = *begin; ++begin; return r; };'."\n".
                      'auto btfun    = [&](bool act) { if(act) { begin -= (savestate-remain); remain = savestate; } else savestate = remain; };'
);

/* Forward/bidir/const random iterator */
$inputs['InF'] = Array(
  'templateparams' => Array('ForwardIterator'),
  'enables'        => Array('DeflIsForwardIterator'),
  'params'         => Array('ForwardIterator&& begin'),
  'abortable'      => ('0'),
  'before'         => 'ForwardIterator saved;'.
                      'auto inputfun = [&]() { auto r = *begin; ++begin; return r; };'."\n".
                      'auto btfun    = [&](bool act) { if(act) begin = saved; else saved = std::move(begin); };'
);

/* Forward/bidir/const random iterator  begin and end */
$inputs['InF2'] = Array(
  'templateparams' => Array('ForwardIterator'),
  'enables'        => Array('DeflIsForwardIterator'),
  'params'         => Array('ForwardIterator&& begin', 'ForwardIterator&& end'),
  'abortable'      => ('1'),
  'before'         => 'ForwardIterator saved;'."\n".
                      'auto inputfun = [&]() { if(begin==end) { return -1; } int r = *begin; ++begin; return r; };'."\n".
                      'auto btfun    = [&](bool act) { if(act) begin = saved; else saved = std::move(begin); };'
);

/*********************************/

/* Output functor and window functor */
$outputs['Outfw'] = Array(
  'templateparams' => Array('OutputFunctor',          'WindowFunctor'),
  'enables'        => Array('DeflIsOutputFunctor',    'DeflIsWindowFunctor'),
  'params'         => Array('OutputFunctor&& output', 'WindowFunctor&& outputcopy'),
  'abortable'      => '(DeflOutputAbortable_OutputFunctor & DeflOutputAbortable_WindowFunctor)',
  'before'         => ''
);

/* Output functor */
$outputs['Outf'] = Array(
  'templateparams' => Array('OutputFunctor'),
  'enables'        => Array('DeflIsOutputFunctor'),
  'params'         => Array('OutputFunctor&& output_orig'),
  'abortable'      => 'DeflOutputAbortable_OutputFunctor',
  'before'         =>
    'DeflDeclWindow'."\n".
    'auto output = [&](unsigned char l)'."\n".
    '{'."\n".
    '    window.Data[window.Head++ % gunzip_ns::MAX_WINDOW_SIZE] = l;'."\n".
    '    return output_orig(l);'."\n".
    '};'."\n".
    'auto outputcopy = [&](std::uint_least16_t length, std::uint_fast32_t offs)'."\n".
    '{'."\n".
    '    /* length=0 means that offs is the size of the window. */'."\n".
    '    for(; length>0; --length)'."\n".
    '    {'."\n".
    '        unsigned char byte = window.Data[(window.Head - offs) % gunzip_ns::MAX_WINDOW_SIZE];'."\n".
    '        if(gunzip_ns::OutputHelper<bool(Abortable&2)>::output(output, byte))'."\n".
    '            break;'."\n".
    '    }'."\n".
    '    return length;'."\n".
    '};'
);

/* Output iterator */
$outputs['OutI'] = Array(
  'templateparams' => Array('OutputIterator'),
  'enables'        => Array('DeflIsOutputIterator'),
  'params'         => Array('OutputIterator&& target'),
  'abortable'      => '0',
  'before'         =>
    'DeflDeclWindow'."\n".
    'auto output = [&](unsigned char l)'."\n".
    '{'."\n".
    '    window.Data[window.Head++ % gunzip_ns::MAX_WINDOW_SIZE] = l;'."\n".
    '    *target = l; ++target;'."\n".
    '};'."\n".
    'auto outputcopy = [&](std::uint_least16_t length, std::uint_fast32_t offs)'."\n".
    '{'."\n".
    '    /* length=0 means that offs is the size of the window. */'."\n".
    '    for(; length>0; --length)'."\n".
    '    {'."\n".
    '        unsigned char byte = window.Data[(window.Head - offs) % gunzip_ns::MAX_WINDOW_SIZE];'."\n".
    '        output(byte);'."\n".
    '    }'."\n".
    '    return false;'."\n".
    '};'
);

/* Random access iterator */
$outputs['Outr'] = Array(
  'templateparams' => Array('RandomAccessIterator'),
  'enables'        => Array('DeflIsRandomAccessIterator'),
  'params'         => Array('RandomAccessIterator&& target'),
  'abortable'      => '0',
  'before'         =>
    'auto output     = [&](unsigned char l) { *target = l; ++target; };'."\n".
    'auto outputcopy = [&](std::uint_least16_t length, std::uint_fast32_t offs)'."\n".
    '{'."\n".
    '    /* length=0 means that offs is the size of the window. */'."\n".
    '    for(; length--; ++target) { *target = *(target-offs); }'."\n".
    '};'
);

/* Random access iterator and length limit */
$outputs['Outrl'] = Array(
  'templateparams' => Array('RandomAccessIterator', 'SizeType2'),
  'enables'        => Array('DeflIsRandomAccessIterator', 'DeflIsSizeType2'),
  'params'         => Array('RandomAccessIterator&& target', 'SizeType2&& target_limit'),
  'abortable'      => '2',
  'before'         =>
    'typename std::iterator_traits<std::decay_t<RandomAccessIterator>>::difference_type used{}, cap=target_limit;'."\n".
    'auto output = [&](unsigned char l)'."\n".
    '{'."\n".
    '    if(used >= cap) return true;'."\n".
    '    target[used] = l; ++used;'."\n".
    '    return false;'."\n".
    '};'."\n".
    'auto outputcopy = [&](std::uint_least16_t length, std::uint_fast32_t offs)'."\n".
    '{'."\n".
    '    /* length=0 means that offs is the size of the window. */'."\n".
    '    for(; length > 0 && used < cap; ++used, --length)'."\n".
    '    {'."\n".
    '        target[used] = target[used - offs];'."\n".
    '    }'."\n".
    '    return length;'."\n".
    '};'
);

/* Random access iterator  begin and end */
$outputs['Outr2'] = Array(
  'templateparams' => Array('RandomAccessIterator'),
  'enables'        => Array('DeflIsRandomAccessIterator'),
  'params'         => Array('RandomAccessIterator&& target_begin', 'RandomAccessIterator&& target_end'),
  'abortable'      => '2',
  'before'         =>
    'auto output = [&](unsigned char l)'."\n".
    '{'."\n".
    '    if(target_begin == target_end) return true;'."\n".
    '    *target_begin = l; ++target_begin;'."\n".
    '    return false;'."\n".
    '};'."\n".
    'auto outputcopy = [&](std::uint_least16_t length, std::uint_fast32_t offs)'."\n".
    '{'."\n".
    '    /* length=0 means that offs is the size of the window. */'."\n".
    '    for(; length > 0 && !(target_begin == target_end); --length, ++target_begin)'."\n".
    '    {'."\n".
    '        *target_begin = *(target_begin - offs);'."\n".
    '    }'."\n".
    '    return length;'."\n".
    '};'
);

/*********************************/

$bodies = Array();

$bodies['Tk0'] = Array(
  'params'         => Array('DeflateTrackNoSize = {}'),
  'ret'  => 'int',
  'body' => 'return gunzip_ns::Gunzip<Abortable>(inputfun, output, outputcopy, btfun);'
);

$bodies['Tki'] = Array(
  'params'         => Array('DeflateTrackInSize'),
  'ret'  => 'std::pair<int, std::uint_fast64_t>',
  'body' => 'gunzip_ns::SizeTracker<DeflateTrackInSize> tracker;'."\n".
            'return tracker(gunzip_ns::Gunzip<Abortable>(tracker.template ForwardInput(inputfun), output, outputcopy, btfun));'
);

$bodies['Tko'] = Array(
  'params'         => Array('DeflateTrackOutSize'),
  'ret'  => 'std::pair<int, std::uint_fast64_t>',
  'body' => 'gunzip_ns::SizeTracker<DeflateTrackOutSize> tracker;'."\n".
            'return tracker(gunzip_ns::Gunzip<Abortable>(inputfun, tracker.template ForwardOutput(output), tracker.template ForwardWindow(outputcopy), btfun));'
);

$bodies['Tkb'] = Array(
  'params'         => Array('DeflateTrackBothSize'),
  'ret'  => 'std::pair<int, std::pair<std::uint_fast64_t,std::uint_fast64_t>>',
  'body' => 'gunzip_ns::SizeTracker<DeflateTrackBothSize> tracker;'."\n".
            'return tracker(gunzip_ns::Gunzip<Abortable>(tracker.template ForwardInput(inputfun), tracker.template ForwardOutput(output), tracker.template ForwardWindow(outputcopy), btfun));'
);

$replacements = Array();
function Replace(&$string, $hint)
{
  global $replacements;
  if($string == '') return;
  if(!isset($replacements[$string]))
  {
    $v = "DEFL_MACRO_$hint";
    $replacements[$string] = $v;
    
    $s = "\n$string";
    $s = str_replace("\n", " \\\n    ", $s);
    print "#define $v $s\n";
  }
  $string = $replacements[$string];
}



foreach($inputs  as $k=>&$input)  Replace($input['before'], $k);
foreach($outputs as $k=>&$output) Replace($output['before'], $k);
foreach($bodies  as $k=>&$body)   Replace($body['body'], $k);
unset($input); unset($output); unset($body);


foreach($inputs  as $input)
foreach($outputs as $output)
foreach($bodies  as $body)
{
  $s = 'template<';
  foreach($input['templateparams'] as $p) { print "{$s}typename {$p}"; $s=','; }
  foreach($output['templateparams'] as $p) { print "{$s}typename {$p}"; $s=','; }
  $s = ">\nstd::enable_if_t<";
  foreach($input['enables']  as $p) { print "{$s}{$p}"; $s=' && '; }
  foreach($output['enables'] as $p) { print "{$s}{$p}"; $s=' && '; }
  $s = ", {$body['ret']}>\n    Deflate(";
  foreach($input['params']  as $p) { print "{$s}{$p}"; $s=','; }
  foreach($output['params'] as $p) { print "{$s}{$p}"; $s=','; }
  foreach($body['params']   as $p) { print "{$s}{$p}"; $s=','; }
  print ")\n{\nconstexpr unsigned char Abortable = {$input['abortable']} | {$output['abortable']};\n{$input['before']} {$output['before']} {$body['body']}\n}\n\n";
}

foreach($replacements as $s=>$v) print "#undef $v\n";
