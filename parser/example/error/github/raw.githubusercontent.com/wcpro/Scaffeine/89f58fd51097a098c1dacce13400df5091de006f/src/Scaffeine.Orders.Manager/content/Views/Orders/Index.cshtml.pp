@{
    ViewBag.Title = "Index";
    Layout = "~/Views/Shared/_Folder.cshtml";
}

<ul class="nav nav-tabs">
    <li><a href="#home" data-toggle="tab">Overview</a></li>
    <li><a href="#list" data-toggle="tab">List</a></li>
    <li class="active"><a href="#details" data-toggle="tab">Details</a></li>
</ul>
<div class="tab-content">
    <div class="tab-pane" id="home">

        <table class="table-striped table table-condensed table-bordered">
            <thead>
                <tr>
                    <th style="width: 50%"></th>
                    <th style="width: 25%">Last 48 hours</th>
                    <th>Before that</th>
                </tr>
            </thead>
            <tbody>
                <tr>
                    <td>Order Received</td>
                    <td>1</td>
                    <td>2</td>
                </tr>
                <tr>
                    <td>Awaiting Shipping Confirmation</td>
                    <td>1</td>
                    <td>2</td>
                </tr>
                <tr>
                    <td>Completed</td>
                    <td>1</td>
                    <td>2</td>
                </tr>
            </tbody>
        </table>
    </div>
    <div class="tab-pane" id="list">
        list
    </div>
    <div class="tab-pane active" id="details">
        <div class="row-fluid">
            <div class="row span6">
                <table class="table table-bordered">
                    <tr>
                        <th style="width: 33%">OrderId</th>
                        <th style="width: 33%">Order Date</th>
                        <th style="width: 33%">Order Status</th>
                    </tr>
                    <tr>
                        <td>1</td>
                        <td>@DateTime.Now.ToShortDateString()</td>
                        <td>Pending</td>
                    </tr>
                </table>

                <table class="table table-bordered">
                    <tr>
                        <th>Shipping Price</th>
                        <td>$8.00
                        </td>
                    </tr>
                    <tr>
                        <th>Shipping Label</th>
                        <td>Rod Johnson<br />
                            72 Summer Place<br />
                            Saratoga Springs, UT 84045
                        </td>
                    </tr>
                </table>

                <table class="table table-bordered table-striped">
                    <thead>
                        <tr>
                            <th colspan="3">Order Items</th>
                        </tr>
                        <tr>
                            <th style="width: 33%">Name</th>
                            <th style="width: 33%">Quantity</th>
                            <th style="width: 33%">Status</th>
                        </tr>
                    </thead>
                    <tbody>
                        <tr>
                            <td>Batman DVD</td>
                            <td>1</td>
                            <td>Awaiting Shipment</td>
                        </tr>
                        <tr>
                            <td>My Old VCR</td>
                            <td>1</td>
                            <td>Awaiting Shipment</td>
                        </tr>

                    </tbody>
                </table>
            </div>
            <div class="row span6">
                <table class="table table-bordered">
                    <tr>
                        <td style="width: 20px"><i style="color: green; font-size: x-large" class="icon-check"></i></td>
                        <td>
                            <i class="icon-credit-card"></i>
                            Credit Card Authorized
                        </td>
                        <td style="width: 200px">Completed (October 10, 2012 9:30 AM)</td>
                    </tr>
                    <tr>
                        <td style="width: 20px"><i style="color: green; font-size: x-large" class="icon-check-empty"></i></td>
                        <td>
                            <i class="icon-truck"></i>
                            Mark 'Batman Returns DVD' As Shipped
                        </td>
                        <td>
                            <button class="btn btn-small btn-primary">Print Shipping Label</button>
                            <button class="btn btn-small btn-primary">
                                Mark As Shipped
                            </button>
                        </td>
                    </tr>
                    <tr>
                        <td style="width: 20px"><i style="color: green; font-size: x-large" class="icon-check-empty"></i></td>
                        <td>
                            <i class="icon-truck"></i>
                            Mark 'My Old VCR' as Shipped
                        </td>
                        <td>
                            <ul>
                                <li><button class="btn btn-small btn-primary">Print Shipping Label</button></li>
                                <li><button class="btn btn-small btn-primary">
                                Mark As Shipped
                            </button></li>
                            </ul>
                            
                            
                        </td>
                    </tr>
                    <tr class="muted">
                        <td style="width: 20px"><i style="font-size: x-large" class="icon-check-empty"></i></td>
                        <td>
                            <i class="icon-credit-card"></i>
                            Credit Card Settled
                        </td>
                        <td></td>
                    </tr>
                </table>
            </div>
        </div>




    </div>
</div>

