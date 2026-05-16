$(document).ready(function () {

    $('#editForm').on('submit', function (e) {
        console.log($('#editOrderBy').val());
        e.preventDefault();
        const apitoken = $("[name='apitoken']").val()
        let id = $('#editId').val();
        let menu = $('#editMenu').val();
        let route = $('#editRoute').val();
        let icon = $('#editIcon').val();
        let status = $('#editStatus').val();
        let url = $('#editUrl').val();
        let is_child = $('#editChild').val();
        let is_frontend = $('#editFrontend').val();
        let order_by = $('#editOrderBy').val();
        $.ajax({
            url: 'api/MenuMaster/updateSubMenu',
            method: 'POST',
            data: {
                id: id,
                menu: menu,
                route: route,
                icon: icon,
                status: status,
                url: url,
                is_child: is_child,
                is_frontend: is_frontend,
                order_by: order_by
            },
            headers: {
                'Authorization': 'Bearer ' + apitoken
            },
            success: function (data) {
                location.reload();

                if (data.status == 200) {
                    toastr.success("Data Updated Successfully")
                    $("#editModal").modal('hide')

                }
                else {
                    toastr.error("Please Try Again After Some Time")
                    $("#editModal").modal('hide')
                    return false
                }

            }

        });
    });
});

$(function () {

    $("[name='f_url']").closest('.col-sm-4').hide()
    $("[name='isFrontEnd']").change(function () {
        if ($(this).val() == 'Y') {
            $("[name='f_url']").closest('.col-sm-4').show()
        }
        else {
            $("[name='f_url']").closest('.col-sm-4').hide()
        }
    })
    var subMenu = '';
    const apitoken = $("[name='apitoken']").val()
    $.ajax({
        type: 'GET',
        url: 'api/MenuMaster/getSubMenu',
        headers: {
            'Authorization': 'Bearer ' + apitoken
        },
        success: function (data2) {
            if (data2.status == 200) {
                subMenu = data2.data
            }
        }
    })

    $.ajax({
        url: 'api/MenuMaster/getMenu',
        method: 'GET',
        headers: {
            'Authorization': 'Bearer ' + apitoken
        },
        success: function (data) {
            console.log(data);
            if (data.status == 200) {
                var tablebody = $("#example1 tbody");
                tablebody.empty()
                $.each(data.data, function (index, value) {
                    var row = $("<tr></tr>");
                    row.append($("<td></td>").text(value.menu));
                    row.append($("<td></td>").text(value.route));
                    row.append($("<td></td>").text(value.icon));
                    row.append($("<td></td>").text(value.status));
                    row.append($("<td></td>").text(value.front_end_url));
                    row.append($("<td></td>").text(value.is_child));
                    row.append($("<td></td>").text(value.isFrontEnd));
                    row.append($("<td></td>").text(value.order_by));
                    row.append($("<td menuId='" + value.id + "'><button class='btn btn-sm btn-secondary editbtn' data-id='" + value.id + "' data-menu='" + value.menu + "' data-route='" + value.route + "' data-icon='" + value.icon + "' data-status='" + value.status + "' data-url='" + value.front_end_url + "' data-is-child='" + value.is_child + "' data-is-frontend='" + value.isFrontEnd + "' data-order-by='" + value.order_by + "'> Edit </button> <button class='btn btn-sm btn-danger deletebtn' data-id='" + value.id + "'>Delete</button></td>"));
                    tablebody.append(row);

                    $('.editbtn').on('click', function () {
                        $('#editId').val($(this).data('id'));
                        $('#editMenu').val($(this).data('menu'));
                        $('#editRoute').val($(this).data('route'));
                        $('#editIcon').val($(this).data('icon'));
                        $('#editStatus').val($(this).data('status'));
                        $('#editUrl').val($(this).data('url'));
                        $('#editChild').val($(this).data('is-child'));
                        $('#editFrontend').val($(this).data('is-frontend'));
                        $('#editOrderBy').val($(this).data('order-by'));
                        $('#editModal').modal('show');
                    });


                })
                $('.deletebtn').on('click', function () {
                    let id = $(this).data('id');

                    if (confirm('Are you sure you want to delete this data?')) {
                        $.ajax({
                            url: 'api/MenuMaster/deleteSubMenu',
                            type: 'DELETE',
                            data: {
                                id: id
                            },
                            headers: {
                                'Authorization': 'Bearer ' + apitoken
                            },
                            success: function (data) {
                                location.reload();

                                if (data.status == 200) {
                                    toastr.success("Data Deleted Successfully")
                                    $("#editModal").modal('hide')
                                    current.remove();

                                }
                                else {
                                    toastr.error("Please Try Again After Some Time")
                                    return false
                                }

                            },
                            error: function (data) {
                                toastr.error("Some Error Occured Please Try Again After Some Time")
                                return false;
                            }
                        });
                    }
                });
                $(".subMenuActions").click(function () {
                    const current = $(this);
                    const text = current.text();
                    $("[name='edtSubMenu']").val(text);

                    $("#modal-default").modal('show')
                    $(".updtSubMenu").click(function () {
                        const name = $("[name='edtSubMenu']");
                        if (name.val() == '') {
                            name.focus()
                            toastr.error("please Enter The Sub Menu Name")
                            return false
                        }
                        const ReqData = {
                            id: current.attr('menuId'),
                            menu: name.val()
                        }
                        var formdata = JSON.stringify(ReqData)

                        $.ajax({
                            url: 'api/MenuMaster/updateSubMenu',
                            type: 'POST',
                            data: formdata,
                            contentType: 'application/json',
                            success: function (data) {
                                if (data.status == 200) {
                                    toastr.success("SubMenu Updated Successfully")
                                    $("#modal-default").modal('hide')
                                }
                                else if (data.status == 422) {
                                    toastr.error(data.message)
                                    $("#modal-default").modal('hide')
                                    return false
                                }
                                else {
                                    toastr.error("Please Try Again After Some Time")
                                    return false
                                }

                            },
                            error: function (data) {
                                toastr.error("Some Error Occured Please Try Again After Some Time")
                                return false;
                            }
                        })
                    })
                    $(".delSubMenu").click(function () {

                        const id = current.attr('menuId')
                        $.ajax({
                            url: 'api/MenuMaster/deleteSubMenu/',
                            type: 'DELETE',
                            data: {
                                id: id
                            },
                            headers: {
                                'Authorization': 'Bearer ' + apitoken
                            },
                            success: function (data) {
                                if (data.status == 200) {
                                    toastr.success("SubMenu Deleted Successfully")
                                    $("#modal-default").modal('hide')
                                    current.remove();

                                }
                                else {
                                    toastr.error("Please Try Again After Some Time")
                                    return false
                                }

                            },
                            error: function (data) {
                                toastr.error("Some Error Occured Please Try Again After Some Time")
                                return false;
                            }
                        })
                    })
                })
            }
        }
    })

    $(".AddMenu").click(function () {
        const name = $("[name='menu']");
        const route = $("[name='route']");
        const icon = $("[name='icon']");
        const isFrontend = $("[name='FrontendUrlMainMenu']")
        if (name.val() == '') {
            name.focus()
            toastr.error("please Enter The Main Menu Name")
            return false
        }
        // if (isFrontend.val() == '') {
        //     isFrontend.focus()
        //     toastr.error("please Enter The Url")
        //     return false
        // }

        const formdata = $("[name='menuMaster']").serialize();
        var apitokens = $("[name='apitoken']").val();
        console.log(apitoken);
        $.ajax({
            type: 'POST',
            url: 'api/MenuMaster/createMenu',
            data: formdata,
            headers: {
                'Authorization': 'Bearer ' + apitokens
            },
            success: function (data) {
                if (data.status == 200) {
                    toastr.success("Menu Created Successfully")
                    $("[name='MenuMaster']").reset();
                } else {
                    toastr.error("Please Try Again After Some Time")
                    return false
                }
            },
            error: function (data) {
                toastr.error("Some Error Occured Please Try Again After Some Time")
                return false;
            }
        })
    })
    $("#subMenuID").click(function () {
        $("[name='is_sub_child']").val('')

        $.ajax({
            type: 'GET',
            url: 'api/MenuMaster/getMenu',
            headers: {
                'Authorization': 'Bearer ' + $('input[name="apitoken"]').val()
            },
            success: function (data) {
                if (data.status == 200) {
                    $("[name='menu_nm']").html('')
                    $.each(data.data, function (index, value) {
                        $("<option></option>").val(value.id).text(value.menu).appendTo("[name='menu_nm']")
                    })
                } else {
                    toastr.error("Please Try Again After Some Time")
                    return false
                }
            },
            error: function (xhr, status, error) {
                // handle error
                toastr.error("Please Try Again After Some Time")
                return false
            }
        })

    })
    $("#SubChildMenu").click(function () {
        $("[name='is_sub_child']").val('Y')
        $.ajax({
            type: 'GET',
            url: 'api/MenuMaster/getSubMenu',
            headers: {
                'Authorization': 'Bearer ' + $('input[name="apitoken"]').val()
            },
            success: function (data) {
                if (data.status == 200) {
                    $("[name='menu_nm']").html('');
                    $.each(data.data, function (index, value) {
                        console.log(value);
                        $("<option></option>").val(value.id).text(value.menu).appendTo("[name='menu_nm']");
                    });
                } else {
                    toastr.error("Please Try Again After Some Time");
                    return false;
                }
            },
            error: function (xhr, status, error) {
                toastr.error("Please Try Again After Some Time");
                return false;
            }
        });
    })
    $(".AddSubMenu").click(function () {
        const name = $("[name='subMenuName']");
        const MenuId = $("[name='menu_nm']");
        if (MenuId.val() == '') {
            MenuId.focus()
            toastr.error("please Select The Menu")
            return false
        }
        if (name.val() == '') {
            name.focus()
            toastr.error("please Enter The Sub Menu Name")
            return false
        }
        const formdata = $("[name='menuMaster']").serialize();
        const is_sub_child = $("[name='is_sub_child']").val();
        if (is_sub_child == 'Y') {
            var url = "api/MenuMaster/createSubChildMenu"
        }
        else {
            var url = "api/MenuMaster/createSubMenu"
        }
        $.ajax({
            type: 'POST',
            url: url,
            data: formdata,
            headers: {
                'Authorization': 'Bearer ' + $('input[name="apitoken"]').val()
            },
            success: function (data) {
                if (data.status == 200) {
                    toastr.success("Sub Menu Created Successfully")
                    $("[name='menuMaster']").reset();
                } else {
                    toastr.error("Please Try Again After Some Time")
                    return false
                }
            }
        })
    })


})
