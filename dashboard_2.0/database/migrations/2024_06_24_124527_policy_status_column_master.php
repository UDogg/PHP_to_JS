 <?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        //
        if(!Schema::hasTable('policystatus_column_master'))
        {
            Schema::create('policystatus_column_master', function (Blueprint $table) {
                $table->id();
                $table->string('column_name',250);
                $table->string('is_default',3)->nullable()->default('N');
                $table->string('is_visible',3)->nullable()->default('N');
                $table->string('alias',150)->nullable();
                $table->string('lob',1000)->nullable();
                $table->timestamps();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
        Schema::dropIfExists('policystatus_column_master');
    }
};
