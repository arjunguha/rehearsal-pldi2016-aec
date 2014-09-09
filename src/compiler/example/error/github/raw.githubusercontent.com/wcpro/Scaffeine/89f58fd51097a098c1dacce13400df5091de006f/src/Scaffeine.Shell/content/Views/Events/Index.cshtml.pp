@{
    ViewBag.Title = "Events";
}
<div class="row">
    <div class="span2">
        <div class="tabbable tabs-left pull-left">
            <ul class="nav nav-tabs" style="width: 100%">
                <li class="active"><a href="#">System Events</a> </li>
                <li><a href="#">Catalog Events</a> </li>
                <li><a href="#">Freshbooks Events</a> </li>
            </ul>
        </div>
    </div>
    <div class="span10">
        <table class="table table-bordered">
            <tr>
                <th rowspan="5">
                    Catalog
                </th>
                <th>
                    Category
                </th>
                <th>
                    Last 24 Hours
                </th>
                <th>
                    Last Week
                </th>
                <th>
                    Last Month
                </th>
            </tr>
            <tr>
                <td>
                    Category.Deleted
                </td>
                <td>
                    123
                </td>
                <td>
                    1243
                </td>
                <td>
                    123
                </td>
            </tr>
            <tr>
                <td>
                    Category.Created
                    <div class="btn-group pull-right" data-toggle="buttons-checkbox">
                        <button class="btn btn-primary">
                            <i class="icon-eye-open icon-white"></i> Add Watch</button>
                        
                        <button class="btn btn-primary">
                            <i class="icon-retweet icon-white"></i> Add Trigger</button>
                    </div>
                </td>
                <td>
                    123
                </td>
                <td>
                    1243
                </td>
                <td>
                    234
                </td>
            </tr>
            <tr>
                <th>
                    Department
                </th>
                <th>
                    Last 24 Hours
                </th>
                <th>
                    Last Week
                </th>
                <th>
                    Last Month
                </th>
            </tr>
            <tr>
                <td>
                    Department.Deleted
                </td>
                <td>
                    123
                </td>
                <td>
                    1243
                </td>
                <td>
                    345
                </td>
            </tr>
        </table>
    </div>
</div>
