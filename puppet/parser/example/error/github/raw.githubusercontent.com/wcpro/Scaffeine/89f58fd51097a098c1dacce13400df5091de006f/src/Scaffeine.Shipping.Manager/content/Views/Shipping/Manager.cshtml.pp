@{
    ViewBag.Title = "SinglePage";
	Layout = "~/Views/Shared/_Folder.cshtml";
}
@if (false)
{ 
    <script src="/Scripts/knockout-2.0.0.js" type="text/javascript"></script>           
}
@section Scripts{
    <script type="text/javascript">
		var currentPage = 1,
            pageSize = 10;
			
        //Entity, Scaffolded!!!
        var ShippingEntity = function () {
            this.Id = 0;
            this.Created = null;
						this.Updated = ko.observable();
						this.ShippingType = ko.observable();
						this.Carrier = ko.observable();
						this.DeliveryAddress = ko.observable();
						this.SendingAddress = ko.observable();
						this.DeliveryDate = ko.observable();
						this.ShippingPrice = ko.observable();
						this.ShippingDescription = ko.observable();
									        };

        $(function () {
            //Setup viewmodel and trigger knockoutjs
            ViewModel.Debug = debugEnabled;
            ViewModel.Setup("Shipping", ShippingEntity, pageSize, function (pageinfo) {
				setupPaging(pageinfo);
                var cmd = getQuerystring("cmd", null);
                var id = getQuerystring("id", null);
                var sender = getQuerystring("sender", null);
                if (cmd == 'add') {
                    ViewLogic.ShowAddDialog(id,sender);
                }
                if (cmd == 'details') {
                    if (id != null) {
                        ViewModel.Activate(id);
                        ViewLogic.ShowDetails();
                    }
                }
                if (cmd == 'delete') {
                    if (id != null) {
                        ViewModel.Activate(id);
                        ViewLogic.ShowDeleteDialog();
                    }
                }
                if (cmd == 'edit') {
                    if (id != null) {
                        ViewModel.Activate(id);
                        ViewLogic.ShowEditDialog();
                    }
                }
				if (cmd == "index" || cmd == "") {
                    ViewLogic.ShowIndex();
                }
            });            
        });

       var ViewLogic = {
            ShowAddDialog: function (id, sender) {
                $("#details").hide();
                LoadParentAddData(id, sender, function () { $('#dialog-modal-add').modal('show'); });
            },
            ShowEditDialog: function () {
                $("#details").hide();
                LoadParentEditData(function () { $('#dialog-modal-edit').modal('show'); });
            },
            HideAddDialog: function () {
                $('#dialog-modal-add').modal('hide');
            },
            HideEditDialog: function () {
                $('#dialog-modal-edit').modal('hide');
            },
            ShowDeleteDialog: function () {
                $("#details").hide();
                $('#dialog-modal-delete').modal('show');
            },
            HideDeleteDialog: function () {
                $('#dialog-modal-delete').modal('hide');
            },
            ShowDetails: function () {
                $("#index").hide();
                $("#details").show();
            },
            ShowIndex: function () {
                $("#details").hide();
                $("#index").show();
            },
            SaveDialogCommit: function (formElement) {
                ViewModel.Add($(formElement).serialize(), function (result) {
                    ViewLogic.HideAddDialog();
                    for (p in result) {
                        $("#" + p, "#dialog-modal-add").parent().removeClass('error');
                        $("#" + p, "#dialog-modal-add").val('');
                        $("#" + p, "#dialog-modal-add").popover('disable');
                    }
                    triggerChangePage(currentPage);
                }, function (result) {
                    for (p in result.ValidationErrors) {
                        $("#" + p, "#dialog-modal-add").parent().addClass('error');
                        $("#" + p, "#dialog-modal-add").data('title', 'Validation Error');
                        $("#" + p, "#dialog-modal-add").data('content', result.ValidationErrors[p].join(','));
                        $("#" + p, "#dialog-modal-add").popover();
                    }
                });
            },
            UpdateDialogCommit: function (formElement) {
                ViewModel.Update($(formElement).serialize(), function (result) {
                    ViewLogic.HideEditDialog();
                    for (p in result) {
                        $("#" + p, "#dialog-modal-edit").parent().removeClass('error');
                        $("#" + p, "#dialog-modal-edit").val('');
                        $("#" + p, "#dialog-modal-edit").popover('disable');
                    }
                }, function (result) {
                    for (p in result.ValidationErrors) {
                        $("#" + p, "#dialog-modal-edit").parent().addClass('error');
                        $("#" + p, "#dialog-modal-edit").data('title', 'Validation Error');
                        $("#" + p, "#dialog-modal-edit").data('content', result.ValidationErrors[p].join(','));
                        $("#" + p, "#dialog-modal-edit").popover();
                    }
                });
            },
            DeleteDialogCommit: function () {
                ViewModel.Remove(ViewModel.Entity());
                ViewLogic.HideDeleteDialog();
                triggerChangePage(currentPage);
            },
            ChangePage: function (entityName, cmd, id, sender) {
                window.location.href = "/" + entityName + "/SinglePage?cmd=" + cmd + "&id=" + id + "&sender=" + sender;
            }
        };

		var LoadParentEditData = function(callback){					 
						
						callback();
		};
		
		var LoadParentAddData = function(id, sender, callback){
			//for each parent, load data
				   
				
								callback();
		};
        var RelatedData = {
            Load: function (entityName, callback) {
                $.getJSON("/" + entityName + "/GetAll/", {}, function (data) {
                    callback(data);
                });
            }
        };
		
		//Paging start
        var triggerChangePage = function (page) {
            ViewModel.ChangePage(page, pageSize, function (data) {
                setupPaging(data);
            });
        }

        var setupPaging = function (data) {

            // Setup paging... And yes I know it´s quite ugly :)           
            currentPage = data.CurrentPage;
            if (data.PagesCount == 1) {
                $(".pagination").empty();
                return;
            }
            var pagerContainer = $("<ul>");
            var numberOfLinks = 5;
            var start = data.CurrentPage - numberOfLinks;
            if (start < 1)
                start = 1;
            var stop = start + (numberOfLinks * 2) + 1;
            if (stop > data.PagesCount)
                stop = data.PagesCount;

            //Create first and prev links...
            if (data.CurrentPage != 1) {
                var first = $("<a href='#' data-page='1'>").text('first').bind('click', function () { triggerChangePage($(this).data('page')); }); ;
                pagerContainer.append($("<li>").append(first));
                var prev = $("<a href='#' data-page='" + (data.CurrentPage - 1) + "'>").text('prev').bind('click', function () { triggerChangePage($(this).data('page')); }); ;
                pagerContainer.append($("<li>").append(prev));
            }

            //Create page links
            for (p = start; p <= stop; p++) {
                if (data.CurrentPage == p) {
                    var l = $("<a href='#'>").text(p);
                    pagerContainer.append($("<li class='disabled'>").append(l));
                }
                else {
                    var l = $("<a href='#' data-page='" + p + "'>").text(p).bind('click', function () { triggerChangePage($(this).data('page')); });
                    pagerContainer.append($("<li>").append(l));
                }
            }

            //Create next last links
            if (data.CurrentPage != data.PagesCount) {
                var next = $("<a href='#' data-page='" + (data.CurrentPage + 1) + "'>").text('next').bind('click', function () { triggerChangePage($(this).data('page')); });
                pagerContainer.append($("<li>").append(next));
                var last = $("<a href='#' data-page='" + data.PagesCount + "'>").text('last').bind('click', function () { triggerChangePage($(this).data('page')); });
                pagerContainer.append($("<li>").append(last));
            }

            //Add paging...
            $(".pagination").empty().append(pagerContainer);
            //End of paging
        }
        //Paging end
        
    </script>
}
<div id="index">
    <div>
        <ul class="nav nav-tabs">
            <li class="active"><a href="#tabs-1">Shipping</a></li>
        </ul>
        <div class="tab-content">
            <div class="tab-pane active" id="tabs-1">
                <a data-toggle="modal" href="#dialog-modal-add" class="btn btn-primary btn-medium" data-bind="click: function(){ LoadParentAddData(null,'',function(){});}">
                        Add Shipping</a>
            </div>
            <table class="table table-condensed">
                <thead>
                    <tr>
												<th>												
                            Id
                        </th>						
												<th>												
                            ShippingType
                        </th>						
												<th>												
                            Carrier
                        </th>						
												<th>												
                            DeliveryAddress
                        </th>						
												<th>												
                            SendingAddress
                        </th>						
												<th>												
                            DeliveryDate
                        </th>						
												<th>												
                            ShippingPrice
                        </th>						
												<th>												
                            ShippingDescription
                        </th>						
																														<th>
                            Created
                        </th>						
												<th>
                            Updated
                        </th>						
						                        <th>
                        </th>
                    </tr>
                </thead>
                <tbody data-bind="foreach: Entities">
                    <tr>
												<td data-bind="text: Id">
                        </td>											
												<td data-bind="text: ShippingType">
                        </td>											
												<td data-bind="text: Carrier">
                        </td>											
												<td data-bind="text: DeliveryAddress">
                        </td>											
												<td data-bind="text: SendingAddress">
                        </td>											
												<td data-bind="text: DeliveryDate">
                        </td>											
												<td data-bind="text: ShippingPrice">
                        </td>											
												<td data-bind="text: ShippingDescription">
                        </td>											
													
																		<td data-bind="text: Created">
                        </td>                        					
												<td data-bind="text: Updated">
                        </td>                        					
						                        <td>
                            <ul class="nav nav-pills" style="margin-bottom: 0px;">
                                <li class="dropdown" style="margin: 0px;"><a style="margin-top: 0px; margin-bottom: 0px;
                                        padding-bottom: 0px; padding-top: 0px;" class="dropdown-toggle" data-toggle="dropdown"
                                        href="#">Action<b class="caret"></b></a>
                                    <ul class="dropdown-menu">
                                        <li><a data-toggle="modal" href="#dialog-modal-delete" data-bind="click: function(item){ $root.Select(item); }">
                                            Delete</a></li>
                                        <li><a data-toggle="modal" href="#dialog-modal-edit" data-bind="click: function(item){ $root.Select(item); LoadParentEditData(function(){}); }">
                                            Edit</a></li>
                                        <li><a href="#" data-bind="click: function(item){ $root.Select(item); ViewLogic.ShowDetails();}">
                                            Details</a></li>                           
                                    </ul>
                                </li>
                             </ul>
                        </td>                        
                    </tr>
                </tbody>
            </table>
			<div class="pagination pagination-centered">
               
            </div>
        </div>
    </div>
</div>
<div id="details" style="display: none;">
	<div>  
		<ul class="nav nav-tabs">
			<li class="active">
				<a href="#tab-ShippingDetails" data-toggle="tab">Shipping Details</a>				
			</li>
					</ul>
		<div  class="tab-content">
			<div id="tab-ShippingDetails"  class="tab-pane active">
    			<div data-bind="with: Entity">
										
				<label for="ShippingType">
                	ShippingType
            	</label>
            	<input type="text" id="ShippingType" name="ShippingType"  data-bind="value: ShippingType" readonly />        		
										
				<label for="Carrier">
                	Carrier
            	</label>
            	<input type="text" id="Carrier" name="Carrier"  data-bind="value: Carrier" readonly />        		
										
				<label for="DeliveryAddress">
                	DeliveryAddress
            	</label>
            	<input type="text" id="DeliveryAddress" name="DeliveryAddress"  data-bind="value: DeliveryAddress" readonly />        		
										
				<label for="SendingAddress">
                	SendingAddress
            	</label>
            	<input type="text" id="SendingAddress" name="SendingAddress"  data-bind="value: SendingAddress" readonly />        		
										
				<label for="DeliveryDate">
                	DeliveryDate
            	</label>
            	<input type="text" id="DeliveryDate" name="DeliveryDate"  data-bind="value: DeliveryDate" readonly />        		
										
				<label for="ShippingPrice">
                	ShippingPrice
            	</label>
            	<input type="text" id="ShippingPrice" name="ShippingPrice"  data-bind="value: ShippingPrice" readonly />        		
										
				<label for="ShippingDescription">
                	ShippingDescription
            	</label>
            	<input type="text" id="ShippingDescription" name="ShippingDescription"  data-bind="value: ShippingDescription" readonly />        		
									
							<label>
                	Created
            	</label>
            	<input type="text" id="Created" name="Created"  data-bind="value: Created" readonly />        								
							<label>
                	Updated
            	</label>
            	<input type="text" id="Updated" name="Updated"  data-bind="value: Updated" readonly />        								
			        	<div>
            	<button data-bind="click: ViewLogic.ShowIndex" class="btn btn-primary">
                Back To List</button>        	
    		</div>
			</div>
		</div>
				</div>
	</div>
</div>
<div id="dialog-modal-edit" class="modal hide fade" style="display: none;">
    <form data-bind="submit: ViewLogic.UpdateDialogCommit">
	<div class="modal-header">
        <a class="close" data-dismiss="modal">[x]</a>
        <h3>
            Edit Shipping</h3>
    </div>	
    <div class="modal-body" data-bind="with: Entity">
						<input type="hidden" id="Id" name="Id" data-bind="value: Id" />
						<div class="control-group">
				<label for="Created">
					Created
				</label>
				<input type="text" readonly id="Created" name="Created" data-bind="value: Created" />
			</div>
					
			<div class="control-group">
				<label for="ShippingType">
                	ShippingType
            	</label>				
											<input type="text" id="ShippingType" name="ShippingType" placeholder="Enter ShippingType here" data-bind="value: ShippingType" />
										            	
        	</div>
					
			<div class="control-group">
				<label for="Carrier">
                	Carrier
            	</label>				
											<input type="text" id="Carrier" name="Carrier" placeholder="Enter Carrier here" data-bind="value: Carrier" />
										            	
        	</div>
					
			<div class="control-group">
				<label for="DeliveryAddress">
                	DeliveryAddress
            	</label>				
											<input type="text" id="DeliveryAddress" name="DeliveryAddress" placeholder="Enter DeliveryAddress here" data-bind="value: DeliveryAddress" />
										            	
        	</div>
					
			<div class="control-group">
				<label for="SendingAddress">
                	SendingAddress
            	</label>				
											<input type="text" id="SendingAddress" name="SendingAddress" placeholder="Enter SendingAddress here" data-bind="value: SendingAddress" />
										            	
        	</div>
					
			<div class="control-group">
				<label for="DeliveryDate">
                	DeliveryDate
            	</label>				
											<input type="text" id="DeliveryDate" name="DeliveryDate" placeholder="Enter DeliveryDate here" data-bind="value: DeliveryDate" />
										            	
        	</div>
					
			<div class="control-group">
				<label for="ShippingPrice">
                	ShippingPrice
            	</label>				
											<input type="text" id="ShippingPrice" name="ShippingPrice" placeholder="Enter ShippingPrice here" data-bind="value: ShippingPrice" />
										            	
        	</div>
					
			<div class="control-group">
				<label for="ShippingDescription">
                	ShippingDescription
            	</label>				
											<input type="text" id="ShippingDescription" name="ShippingDescription" placeholder="Enter ShippingDescription here" data-bind="value: ShippingDescription" />
										            	
        	</div>
			  
				
				</div>
        <div class="modal-footer">
        	<button class="btn" data-bind="click: ViewLogic.HideEditDialog">
            	Cancel</button>
        	<button type="submit" class="btn btn-primary">
            	Save</button>
    	</div>
    </form>
</div>
<div id="dialog-modal-delete" class="modal hide fade" style="display: none;">
	<div class="modal-header">
        <a class="close" data-dismiss="modal">[x]</a>
        <h3>
            Delete Factory</h3>
    </div>
    <div class="modal-body" data-bind="with: Entity">
        <h3>
            Do you reallt want to delete this Shipping?</h3>
    </div>
    <div class="modal-footer">
        <button class="btn" data-bind="click: ViewLogic.HideDeleteDialog">
            Cancel</button>
        <button type="submit" class="btn btn-primary" data-bind="click: ViewLogic.DeleteDialogCommit">
            Confirm Delete</button>
    </div>
</div>
<div id="dialog-modal-add" class="modal hide fade" style="display: none;">
    <form data-bind="submit: ViewLogic.SaveDialogCommit">
	<div class="modal-header">
        <a class="close" data-dismiss="modal">[x]</a>
        <h3>
            Add Shipping</h3>
    </div>
    <div class="modal-body">       
					<div class="control-group">
            	<label for="ShippingType">
                ShippingType
            	</label>
            								<input type="text" id="ShippingType" name="ShippingType" placeholder="Enter ShippingType here" />
							        	</div>			
						<div class="control-group">
            	<label for="Carrier">
                Carrier
            	</label>
            								<input type="text" id="Carrier" name="Carrier" placeholder="Enter Carrier here" />
							        	</div>			
						<div class="control-group">
            	<label for="DeliveryAddress">
                DeliveryAddress
            	</label>
            								<input type="text" id="DeliveryAddress" name="DeliveryAddress" placeholder="Enter DeliveryAddress here" />
							        	</div>			
						<div class="control-group">
            	<label for="SendingAddress">
                SendingAddress
            	</label>
            								<input type="text" id="SendingAddress" name="SendingAddress" placeholder="Enter SendingAddress here" />
							        	</div>			
						<div class="control-group">
            	<label for="DeliveryDate">
                DeliveryDate
            	</label>
            								<input type="text" id="DeliveryDate" name="DeliveryDate" placeholder="Enter DeliveryDate here" />
							        	</div>			
						<div class="control-group">
            	<label for="ShippingPrice">
                ShippingPrice
            	</label>
            								<input type="text" id="ShippingPrice" name="ShippingPrice" placeholder="Enter ShippingPrice here" />
							        	</div>			
						<div class="control-group">
            	<label for="ShippingDescription">
                ShippingDescription
            	</label>
            								<input type="text" id="ShippingDescription" name="ShippingDescription" placeholder="Enter ShippingDescription here" />
							        	</div>			
							        
    </div>
	<div class="modal-footer">
        <button class="btn" data-bind="click: ViewLogic.HideAddDialog">
            Cancel</button>
        <button type="submit" class="btn btn-primary">
            Save</button>        
    </div>
    </form>
</div>
<div id="debug" data-bind="visible: Debug">
    <hr />
    <h2>
        Debug (To turn of debugging set <i>"var debugEnabled = false;"</i> in _Layout.cshtml)</h2>
    <div data-bind="text: ko.toJSON(ViewModel)">
    </div>
</div>
