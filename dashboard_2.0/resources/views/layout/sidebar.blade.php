<aside class="main-sidebar sidebar-dark-primary elevation-4">
    <!-- Brand Logo -->
    <a href="index3.html" class="brand-link">
      <img src="dist/img/logo.png" alt="AdminLTE Logo" class="brand-image img-circle elevation-3"
      style="opacity: .8">
      <span class="brand-text font-weight-light">Fyntune</span>
    </a>
    <!-- Sidebar -->
    <div class="sidebar">
      <!-- Sidebar user panel (optional) -->
      <div class="user-panel mt-3 pb-3 mb-3 d-flex">
        <div class="image">
          <img src="dist\img\profile.png" class="img-circle elevation-2" alt="User Image">
        </div>
        <div class="info">
        <a href="#" class="d-block">{{credential_decrypt(auth()->user()['name'])}}</a>
        </div>
      </div>

      <!-- SidebarSearch Form -->
      <div class="form-inline">
        <div class="input-group" data-widget="sidebar-search">
          <input class="form-control form-control-sidebar" type="search" placeholder="Search Menu..." aria-label="Search">
          <div class="input-group-append">
            <button class="btn btn-sidebar">
              <i class="fas fa-search fa-fw"></i>
            </button>
          </div>
        </div>
      </div>

      <!-- Sidebar Menu -->
      <nav class="mt-2">
        <ul class="nav nav-pills nav-sidebar flex-column" data-widget="treeview" role="menu" data-accordion="false">
          <!-- Add icons to the links using the .nav-icon class with font-awesome or any other icon font library -->
          {{-- <li class="nav-item menu-open">
            <a href="{{route('dashboard')}}" class="nav-link">
              <i class="nav-icon fas fa-tachometer-alt"></i>
              <p>
                Dashboard
              </p>
            </a>
          </li> --}}
          <li class="nav-item menu-open">
            <a href="template" class="nav-link">
              <i class="nav-icon fas fa-tachometer-alt"></i>
              <p>
                Template
              </p>
            </a>
          </li>
          <li class="nav-item menu-open">
            <a href="{{route('adminlte')}}" class="nav-link">
              <i class="nav-icon fas fa-tachometer-alt"></i>
              <p>
                View Theme
              </p>
            </a>
          </li>

            @php
                $submenu = ['user', 'menu','credential','broker','session','otp','placeholder','sms_template','event'];
                 $current_page = Request::segment(1);
                 $menus = \App\Models\MenuMasterModel::orderBy('order_by')->get();
                 $user = auth()->user();
            @endphp
            @foreach($menus as $Mainmenu)
                @if(empty($Mainmenu->menuId) && $Mainmenu->is_child == 'Y')
                  <li class="nav-item">
                    <a href="javascript:void(0)" class="nav-link trigger main">
                      <i class="nav-icon fas fa-tachometer-alt"></i>
                      <p>
                        {{$Mainmenu->menu}}
                        <i class="right fas fa-angle-left"></i>
                      </p>
                    </a>
                      @else
                          @continue
                @endif
            @foreach($menus as $childMenu)
              @if($childMenu->menuId == $Mainmenu->id && $user->can($childMenu->MenuPermissionName))
              @if(!empty($childMenu->route) && Route::has($childMenu->route))
                <ul id="toggle" class="nav @if(!in_array($current_page, $submenu)) nav-treeview @endif ">
                    <li class="nav-item">
                        <a href="{{ !empty($childMenu->route) && Route::has($childMenu->route) ? route($childMenu->route) : '#' }}"
                           class="pl-3 nav-link @if(url($current_page) == (Route::has($childMenu->route) ? route($childMenu->route) : '#')) active @endif">
                            <i class="far fa-circle nav-icon"></i>
                            <p>{{ $childMenu->menu }}</p>
                        </a>
                    </li>


                </ul>
                    @else
                        @continue
                @endif
                @endif
              @endforeach
            @endforeach
        </ul>
      </nav>
      <!-- /.sidebar-menu -->
    </div>
    <!-- /.sidebar -->
  </aside>
<script src="{{asset('plugins/jquery/jquery.js')}}"></script>
<script>
  $(document).ready(function(){

    $('.trigger.main').on('click', function(e){
      e.preventDefault();

      // Toggle the nav-treeview visibility
      var $submenu = $(this).next('ul');
      $submenu.toggleClass('nav-treeview');

      // Toggle the arrow direction
      var $icon = $(this).find('.right');
      if ($submenu.hasClass('nav-treeview')) {
        $icon.removeClass('fa-angle-down').addClass('fa-angle-left');
      } else {
        $icon.removeClass('fa-angle-left').addClass('fa-angle-down');
      }
    });
  });
</script>
