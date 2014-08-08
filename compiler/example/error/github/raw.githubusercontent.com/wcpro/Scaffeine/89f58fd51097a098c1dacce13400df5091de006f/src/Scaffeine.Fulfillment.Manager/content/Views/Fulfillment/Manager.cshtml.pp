@{
    ViewBag.Title = "Index";
    ViewBag.SitemapProvider = "Modules";
    Layout = "~/Views/Shared/_Folder.cshtml";
}

<div class="alert alert-success">
    Customer Created
</div>

<table class="table table-bordered">
    <thead>
        <tr>
            <th>Customer Name</th>
            <th>Purchase Amount</th>
            <th>Purchase Date</th>
            <th>Status</th>
            <th></th>
        </tr>
    </thead>
    <tr>
        <td>Walter White</td>
        <td>$5.12</td>
        <td>September 4, 2012</td>
        <td><a href="#">Purchased</a></td>
        <td><a href="@Url.Action("Record", "Orders")">More Information</a></td>
    </tr>
</table>