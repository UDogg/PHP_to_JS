@extends('layout.app', ['title' => 'Stage Master'])
<!-- Main content -->
@section('content')
<!-- Main content -->
<!DOCTYPE html>
<html>

<head>
    <link rel="stylesheet" href="{{ asset('css\zone_master.css') }}">
    <meta name="csrf-token" content="{{ csrf_token() }}">
</head>

<body>



    <div class="card card-secondary custom-card">
        <button class="btn btn-primary verticalbtn btn-right" type="button" data-toggle="modal"
            data-target="#exampleModal">
            Vertical
        </button>
    </div>


    {{-- VERTICAL MODEL --}}

    <div class="modal fade" id="exampleModal" tabindex="-1" role="dialog" aria-labelledby="exampleModalLabel"
        aria-hidden="true">
        <div class="modal-dialog modal-lg" role="document">
            <div class="modal-content">
                <div class="modal-header">
                    <h5 class="modal-title" id="exampleModalLabel">Vertical Master</h5>
                    <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                        <span aria-hidden="true">&times;</span>
                    </button>
                </div>
                <div class="modal-body" style="overflow-x: auto; overflow-y: auto; max-height: 80vh;">
                    <form id="vform">
                        <div class="form-group">
                            <label for="verticalName">Vertical Name</label>
                            <input type="text" class="form-control" id="verticalName" placeholder="Enter vertical name">
                        </div>
                        <button type="button" class="btn btn-secondary" data-dismiss="modal">Close</button>
                        <button type="submit" class="btn btn-primary">Save</button>
                    </form>
                </div>

                <div class="card card-secondary">
                    <table id="example1" class="table table-bordered table-striped dataTable dtr-inline"
                        aria-describedby="example1_info">
                        <thead>
                            <tr>
                                <th>Sr.No</th>
                                <th>Vertical Name</th>
                                <th>created By </th>
                                <th>created At</th>
                                <th>Actions</th>
                            </tr>
                        </thead>
                        <tbody>
                            @foreach ($verticalMaster as $item)
                            <tr>
                                <td>{{ $item->id }}</td>
                                <td>{{ $item->vertical_name }}</td>
                                <td>{{ $item->created_by }}</td>
                                <td>{{ $item->created_at }}</td>
                                <td>
                                    <button class="btn btn-sm  verticaleditbtn" data-id="{{$item->id}}"
                                        data-name="{{$item->vertical_name}}"> <i
                                            class="fa-regular fa-pen-to-square ml-2 updt_icn"
                                            style="width: 10px; height: 10px"></i>
                                    </button>
                                    <button class="btn btn-sm  verticaldeletebtn" data-id="{{$item->id}}"> <i
                                            class="fa-solid fa-trash ml-3 del_icn"
                                            style="width: 10px; height: 10px"></i></button>
                                </td>
                            </tr>
                            @endforeach
                        </tbody>
                    </table>
                </div>

            </div>
        </div>
    </div>

    {{-- model for vertical master edit --}}
    <div class="modal fade" id="editverticalModel" tabindex="-1" aria-labelledby="editModalLabel" aria-hidden="true">
        <div class="modal-dialog modal-lg">
            <div class="modal-content">
                <div class="modal-header">
                    <h5 class="modal-title" id="editModalLabel">Vertical Name</h5>
                    <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                        <span aria-hidden="true">&times;</span>
                    </button>
                </div>
                <div class="modal-body" style="overflow-x: auto; overflow-y: auto; max-height: 80vh;">
                    <form id="editVerticalForm">
                        <input type="hidden" id="vid">
                        <div class="form-group">
                            <label for="vname">vertical Name</label>
                            <input type="text" class="form-control" id="vname" required>
                        </div>
                        <button type="button" class="btn btn-secondary" data-dismiss="modal">Close</button>
                        <button type="submit" class="btn btn-primary">Update</button>
                    </form>
                </div>
            </div>
        </div>
    </div>









    <div class="card card-secondary">
        <div class="card-header">
            <h3 class="card-title">Zone Master</h3>
        </div>
        <div class="container">
            <form name="zoneMaster">
                @csrf
                <input type="hidden" name="apitoken" value="{{request()->cookie('Token')}} ">
                <div class="zone-master">
                    <div>
                        <label for="officeZone">Office Zone:</label>
                        <input type="text" id="officeZone" name="officeZone">
                    </div>
                    <div>
                        <label for="officeName">Office Name:</label>
                        <input type="text" id="officeName" name="officeName">
                    </div>
                </div>
                <div class="zone-master">
                    <div>
                        <label for="parentOffice">Parent Office:</label>
                        <input type="text" id="parentOffice" name="parentOffice">
                    </div>
                    <div>
                        <label for="officePincode">Office Pincode:</label>
                        <input type="number" id="officePincode" name="officePincode">
                    </div>
                </div>
                <div class="zone-master">
                    <div>
                        <label for="contactPhone">Contact Phone Number:</label>
                        <input type="number" id="contactPhone" name="contactPhone">
                    </div>
                    <div>
                        <label for="contactEmail">Contact Email:</label>
                        <input type="email" id="contactEmail" name="contactEmail">
                    </div>
                </div>
                <div class="zone-master">
                    <div>
                        <label for="address">Address:</label>
                        <textarea id="address" name="address"></textarea>
                    </div>
                </div>

                <div class="actions">
                    <button type="button" class="btn btn-primary submit_btn">Save</button>
                </div>
            </form>
        </div>
    </div>

    <div class="card card-secondary">
        <table id="example1" class="table table-bordered table-striped dataTable dtr-inline"
            aria-describedby="example1_info">
            <thead>
                <tr>
                    <th>Sr.No</th>
                    <th>Office Zone</th>
                    <th>Office Name</th>
                    <th>Parent Office</th>
                    <th>Office Pincode</th>
                    <th>Contact Phone</th>
                    <th>Contact Email</th>
                    <th>Address</th>
                    <th>Actions</th>
                </tr>
            </thead>
            <tbody>
                @foreach ($data as $item)

                <tr>
                    <td>{{ $item->id }}</td>
                    <td>{{ $item->office_zone }}</td>
                    <td>{{ $item->office_name }}</td>
                    <td>{{ $item->parent_office }}</td>
                    <td>{{ $item->office_pincode }}</td>
                    <td>{{ $item->contact_phone }}</td>
                    <td>{{ $item->contact_email }}</td>
                    <td>{{ $item->address }}</td>
                    <td>
                        <div class="action-buttons">
                            <button class="btn btn-sm btn-primary editbtn" data-id="{{$item->id}}">Edit</button>
                            <button class="btn btn-sm btn-danger deletebtn" data-id="{{$item->id}}">Delete</button>
                        </div>
                    </td>
                </tr>
                @endforeach
            </tbody>
        </table>
    </div>


    {{-- zone master model --}}
    <div class="modal fade" id="editModal" tabindex="-1" aria-labelledby="editModalLabel" aria-hidden="true">
        <div class="modal-dialog">
            <div class="modal-content">
                <div class="modal-header">
                    <h5 class="modal-title" id="editModalLabel">Edit Filter Master Data</h5>
                    <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                        <span aria-hidden="true">&times;</span>
                    </button>
                </div>
                <div class="modal-body">
                    <form id="editForm">
                        <input type="hidden" id="editId" name="id"> <!-- Added 'name' attribute -->
    
                        <div class="form-group">
                            <label for="off_zone">Office Zone</label>
                            <input type="text" class="form-control" id="off_zone" name="off_zone" required>
                        </div>
                        <div class="form-group">
                            <label for="off_name">Office Name</label>
                            <input type="text" class="form-control" id="off_name" name="off_name">
                        </div>
                        <div class="form-group">
                            <label for="parent_office">Parent Office</label>
                            <input type="text" class="form-control" id="parent_office" name="parent_office">
                        </div>
                        <div class="form-group">
                            <label for="office_pincode">Office Pincode</label>
                            <input type="text" class="form-control" id="office_pincode" name="office_pincode">
                        </div>
                        <div class="form-group">
                            <label for="contact_phone">Contact Phone</label>
                            <input type="text" class="form-control" id="contact_phone" name="contact_phone">
                        </div>
                        <div class="form-group">
                            <label for="contact_email">Contact Email</label>
                            <input type="email" class="form-control" id="contact_email" name="contact_email">
                        </div>
                        <div class="form-group">
                            <label for="address">Address</label>
                            <input type="text" class="form-control" id="address" name="address">
                        </div>
    
                        <button type="button" class="btn btn-secondary" data-dismiss="modal">Close</button>
                        <button type="submit" class="btn btn-primary">Update</button>
                    </form>
                </div>
            </div>
        </div>
    </div>
    
    <script src={{ asset('Js\zone_master.js')}}></script>




    @endsection