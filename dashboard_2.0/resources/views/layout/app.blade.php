@include('layout.header')
@include('layout.navbar')
@include('layout.sidebar')

<!-- Content Wrapper. Contains page content -->
<div class="content-wrapper">
  @include('layout.pageHeader')
    @yield('content')
</div>
@include('layout.footer')
  <!-- /.content-wrapper -->

